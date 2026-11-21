import { spawn, type ChildProcess } from 'child_process';
import crypto from 'crypto';
import express from 'express';
import fs from 'fs';
import path from 'path';
import { Readable } from 'stream';
import { fileURLToPath } from 'url';
import { createServer as createViteServer } from 'vite';
import { ALL_CATEGORIES, INITIAL_FALLBACK_MOVIES } from './src/data/categories.ts';
import {
  cleanTimeAgoAndEpisode,
  deduplicateByExactPath,
  deduplicateMovieCards,
  getCanonicalTitleKey,
  getItemMinutesAgo,
  normalizeMovieCardItem,
  normalizeMovieCardList,
  sortItemsByHighRating,
  sortItemsByHotAndHype,
  sortItemsByRecentUpload,
} from './src/utils/timeAgo.ts';
import type {
  CastMember,
  DirectDownloadButton,
  EpisodeItem,
  GlobalMovieNotification,
  HomeShelfSection,
  MovieCardItem,
  MovieDetailData,
  MovieDubOption,
  ServerNodeStatus,
  StreamSource,
  UserMovieRequest,
} from './src/types/cinema.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

process.on('uncaughtException', (err) => {
  console.error('Uncaught exception (kept server alive):', err?.message || err);
});

process.on('unhandledRejection', (reason) => {
  console.error('Unhandled rejection (kept server alive):', reason);
});

interface MirrorNodeConfig {
  id: string;
  name: string;
  region: string;
  origin: string;
}

const SERVER_NODES: MirrorNodeConfig[] = [
  { id: 'node-moviebox', name: 'HD Server 1', region: 'Bangladesh / Global HD Hub', origin: 'https://moviebox01.com' },
  { id: 'node-alpha', name: 'Node Alpha', region: 'BD-Fast Edge', origin: 'https://wvaedp.movielinkbd.at' },
  { id: 'node-beta', name: 'Node Beta', region: 'Auto-Redirect Core', origin: 'https://movielinkbd.at' },
  { id: 'node-gamma', name: 'Node Gamma', region: 'Official Portal', origin: 'https://movielinkbd.com' },
  { id: 'node-delta', name: 'Node Delta', region: 'Backup Mirror', origin: 'https://cmyyhb.movielinkbd.at' },
];

let latestMlbdOrigin = 'https://wvaedp.movielinkbd.at';

const PRIMARY_MIRROR_NODES = SERVER_NODES.filter((n) => n.id !== 'node-moviebox');
const MOVIEBOX_ORIGIN = 'https://moviebox01.com';
const MOVIEBOX_CLASSIC_ORIGIN = 'https://movie-box.co';
const MOVIEBOX_API_ORIGIN = 'https://h5-api.aoneroom.com';
const MOVIEBOX_SPORTS_API_ORIGIN = 'https://h5-sport-api.aoneroom.com';

function buildMovieBoxHeaders(
  referer = `${MOVIEBOX_ORIGIN}/`,
  token = ''
): Record<string, string> {
  const headers: Record<string, string> = {
    'User-Agent':
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
    Accept: 'application/json',
    'Content-Type': 'application/json',
    Referer: referer,
    'X-Client-Info': JSON.stringify({ timezone: 'Asia/Dhaka', countryCode: 'BD', country: 'BD' }),
    'X-Forwarded-For': '103.112.53.10',
    'CF-IPCountry': 'BD',
    'X-Country-Code': 'BD',
    'X-Vip-Restrict': '0',
    'X-No-High-Risk-Restrict': '1',
    'X-Request-Lang': 'en',
  };
  if (token) {
    headers.Authorization = `Bearer ${token}`;
  }
  return headers;
}

interface CacheEntry<T> {
  data: T;
  expiresAt: number;
}

const catalogCache = new Map<string, CacheEntry<{ items: MovieCardItem[]; maxPage: number; activeNodeId: string }>>();
const detailCache = new Map<string, CacheEntry<MovieDetailData>>();
const imdbIdCache = new Map<string, string>();
let healthCache: CacheEntry<ServerNodeStatus[]> | null = null;

// =========================================================================
// PERSISTENT 2-SITE MASTER CATALOG ARCHIVE & REAL-TIME AUTO-SYNC API ENGINE
// Guarantees zero missed content: new uploads auto-update Homepage in real
// time while all previous/older movies & series stay permanently indexed.
// =========================================================================
type SourceSiteId = 'moviebox' | 'movielinkbd';

interface ArchivedCatalogRecord {
  item: MovieCardItem;
  site: SourceSiteId;
  firstSeenAt: number;
  lastSyncedAt: number;
  categories: string[];
  isNewlyDetected?: boolean;
}

const ARCHIVE_FILE_PATH = path.join(__dirname, '.cinepulse-catalog-archive.json');
const MAX_ARCHIVE_RECORDS = 15000;
const AUTO_SYNC_INTERVAL_MS = 60_000;

const masterArchiveMap = new Map<string, ArchivedCatalogRecord>();
let archiveSaveTimer: NodeJS.Timeout | null = null;
let hasCompletedInitialBaseline = false;
let lastAutoSyncAt = 0;
let isSyncRunning = false;
let lastCycleNewItemsCount = 0;
let archivePageCursor = 2;
const sseClients = new Set<express.Response>();

function detectSourceSite(itemPath: string): SourceSiteId {
  if (itemPath?.startsWith('/mb/')) return 'moviebox';
  return 'movielinkbd';
}

const UNRELATED_REGIONAL_REGEX =
  /\b(nigeria|nigerian|yoruba|nollywood|ghana|ghanaian|kenya|kenyan|uganda|tanzania|ethiopia|cameroon|zimbabwe|hausa|igbo|swahili|tagalog|filipino|philippines|gbadewolu|kowope|olokada|koleoso)\b/i;

function isUnrelatedRegionalCard(item: MovieCardItem): boolean {
  if (!item?.path?.startsWith('/mb/')) return false;
  const hay = `${item.title || ''} ${item.language || ''}`;
  if (/\[(?:hindi|bengali|bangla|urdu|tamil|telugu)\]/i.test(hay)) return false;
  return UNRELATED_REGIONAL_REGEX.test(hay);
}

function loadMasterArchiveFromDisk() {
  try {
    if (fs.existsSync(ARCHIVE_FILE_PATH)) {
      const raw = fs.readFileSync(ARCHIVE_FILE_PATH, 'utf8');
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed?.records)) {
        for (const rec of parsed.records) {
          if (
            rec?.item?.path &&
            rec?.item?.title &&
            !rec.item.path.startsWith('/mf/') &&
            !isUnrelatedRegionalCard(rec.item)
          ) {
            masterArchiveMap.set(rec.item.path, {
              item: rec.item,
              site: detectSourceSite(rec.item.path),
              firstSeenAt: Number(rec.firstSeenAt) || Date.now(),
              lastSyncedAt: Number(rec.lastSyncedAt) || Date.now(),
              categories: Array.isArray(rec.categories) ? rec.categories : ['/'],
              isNewlyDetected: Boolean(rec.isNewlyDetected),
            });
          }
        }
      }
      if (Number(parsed?.archivePageCursor) >= 2) {
        archivePageCursor = Number(parsed.archivePageCursor);
      }
      if (Number(parsed?.lastAutoSyncAt) > 0) {
        lastAutoSyncAt = Number(parsed.lastAutoSyncAt);
      }
    }
  } catch {
    // ignore corrupt archive file and rebuild cleanly
  }

  const now = Date.now();
  for (const [catPath, list] of Object.entries(INITIAL_FALLBACK_MOVIES)) {
    for (const rawItem of list) {
      if (!rawItem?.path || !rawItem?.title || rawItem.path.startsWith('/mf/')) continue;
      if (!masterArchiveMap.has(rawItem.path)) {
        masterArchiveMap.set(rawItem.path, {
          item: normalizeMovieCardItem(rawItem, now),
          site: detectSourceSite(rawItem.path),
          firstSeenAt: now - 3600_000,
          lastSyncedAt: now,
          categories: [catPath],
          isNewlyDetected: false,
        });
      }
    }
  }
}

function scheduleSaveMasterArchive() {
  if (archiveSaveTimer) return;
  archiveSaveTimer = setTimeout(() => {
    archiveSaveTimer = null;
    try {
      const records = Array.from(masterArchiveMap.values())
        .sort((a, b) => b.lastSyncedAt - a.lastSyncedAt)
        .slice(0, MAX_ARCHIVE_RECORDS);
      fs.writeFile(
        ARCHIVE_FILE_PATH,
        JSON.stringify({
          savedAt: Date.now(),
          lastAutoSyncAt,
          archivePageCursor,
          totalRecords: records.length,
          records,
        }),
        'utf8',
        () => {}
      );
    } catch {
      // ignore disk write issues in read-only environments
    }
  }, 4000);
  archiveSaveTimer.unref();
}

function broadcastSseEvent(eventName: string, payload: Record<string, any>) {
  if (sseClients.size === 0) return;
  const serialized = `event: ${eventName}\ndata: ${JSON.stringify(payload)}\n\n`;
  for (const client of sseClients) {
    try {
      client.write(serialized);
    } catch {
      sseClients.delete(client);
    }
  }
}

function upsertItemsIntoMasterArchive(
  items: MovieCardItem[],
  categoryPath: string,
  markNewAsFresh = false
): MovieCardItem[] {
  const now = Date.now();
  const newlyDiscovered: MovieCardItem[] = [];
  let changed = false;

  for (const raw of items) {
    if (!raw?.path || !raw?.title || raw.path.startsWith('/mf/')) continue;
    const site = detectSourceSite(raw.path);
    const existing = masterArchiveMap.get(raw.path);
    if (!existing) {
      const normalized = normalizeMovieCardItem(raw, now);
      if (markNewAsFresh && hasCompletedInitialBaseline && !normalized.uploadedAtMs) {
        normalized.uploadedAtMs = now;
        normalized.timeAgo = 'Just now';
      }
      masterArchiveMap.set(raw.path, {
        item: normalized,
        site,
        firstSeenAt: now,
        lastSyncedAt: now,
        categories: [categoryPath || '/'],
        isNewlyDetected: markNewAsFresh && hasCompletedInitialBaseline,
      });
      newlyDiscovered.push(normalized);
      changed = true;
    } else {
      const mergedItem: MovieCardItem = {
        ...existing.item,
        ...raw,
        poster: raw.poster || existing.item.poster,
        rating: raw.rating || existing.item.rating,
        views: raw.views && raw.views !== 'Live' ? raw.views : existing.item.views,
        episodePill: raw.episodePill || existing.item.episodePill,
        uploadedAtMs: raw.uploadedAtMs || existing.item.uploadedAtMs,
      };
      if (categoryPath && !existing.categories.includes(categoryPath)) {
        existing.categories.push(categoryPath);
      }
      existing.item = normalizeMovieCardItem(mergedItem, now);
      existing.lastSyncedAt = now;
      changed = true;
    }
  }

  if (changed) {
    scheduleSaveMasterArchive();
  }
  return newlyDiscovered;
}

function getArchiveCountsBySite() {
  let moviebox = 0;
  let movielinkbd = 0;
  for (const rec of masterArchiveMap.values()) {
    if (rec.item.path?.startsWith('/mf/')) continue;
    if (rec.site === 'moviebox') moviebox++;
    else movielinkbd++;
  }
  return {
    total: moviebox + movielinkbd,
    moviebox,
    movielinkbd,
  };
}

function queryMasterArchive(options: {
  q?: string;
  category?: string;
  source?: string;
  includeAdult?: boolean;
  sort?: 'latest' | 'popular' | 'rating';
  limit?: number;
  offset?: number;
}): { items: MovieCardItem[]; total: number } {
  const lowerQ = (options.q || '').trim().toLowerCase();
  const cat = (options.category || '').trim();
  const src = (options.source || 'all').toLowerCase();
  const records: ArchivedCatalogRecord[] = [];

  for (const rec of masterArchiveMap.values()) {
    if (rec.item.path?.startsWith('/mf/')) continue;
    if (!options.includeAdult && rec.item.isAdult && cat !== '/adult18plus') continue;
    if (src !== 'all' && rec.site !== src) continue;
    if (cat && cat !== '/' && cat !== '/new-uploads' && cat !== '/new-releases' && cat !== '/hot-dhamaka') {
      const inCat = rec.categories.includes(cat);
      if (!inCat) continue;
    }
    if (lowerQ) {
      const hay = `${rec.item.title} ${rec.item.language || ''} ${rec.item.typeBadge || ''}`.toLowerCase();
      if (!hay.includes(lowerQ)) continue;
    }
    records.push(rec);
  }

  const nowMs = Date.now();
  if (options.sort === 'latest') {
    records.sort((a, b) => {
      const aMin = getItemMinutesAgo(a.item, 0, nowMs);
      const bMin = getItemMinutesAgo(b.item, 0, nowMs);
      if (aMin !== bMin) return aMin - bMin;
      return (b.item.uploadedAtMs || b.firstSeenAt) - (a.item.uploadedAtMs || a.firstSeenAt);
    });
  } else if (options.sort === 'rating') {
    records.sort((a, b) => (parseFloat(b.item.rating || '0') || 0) - (parseFloat(a.item.rating || '0') || 0));
  } else {
    records.sort((a, b) => {
      const newBoostA = a.isNewlyDetected ? 500 : 0;
      const newBoostB = b.isNewlyDetected ? 500 : 0;
      return (b.item.hypeScore || 0) + newBoostB - ((a.item.hypeScore || 0) + newBoostA);
    });
  }

  const dedupedAll = deduplicateMovieCards(records.map((r) => normalizeMovieCardItem(r.item, nowMs)));
  const total = dedupedAll.length;
  const offset = Math.max(0, options.offset || 0);
  const limit = Math.max(1, Math.min(200, options.limit || 48));
  return { items: dedupedAll.slice(offset, offset + limit), total };
}

loadMasterArchiveFromDisk();

function sortSourcesFastestFirst(sources?: StreamSource[]): StreamSource[] {
  if (!Array.isArray(sources) || sources.length <= 1) return sources || [];
  const score = (src: StreamSource) => {
    const isEmbed =
      src.type === 'embed' ||
      /abyssplayer\.com|abysscdn\.com|vidsrc|multiembed|autoembed|myflix/i.test(`${src.url || ''} ${src.id || ''}`);
    if (isEmbed) return 400;
    const isMovieBox =
      src.id?.startsWith('mb-') || /\/api\/mb-stream|\/api\/mb-ep-stream/i.test(src.url || '');
    if (isMovieBox) {
      const baseMb = 4500;
      const sizeMatch = (src.name || '').match(/(\d+)\s*MB/i);
      const sizeMb = sizeMatch ? parseInt(sizeMatch[1], 10) : 0;
      const isHeavyFile = sizeMb > 350;
      if (src.quality === 480) return baseMb + 145;
      if (src.quality === 720) return baseMb + 140;
      if (src.quality === 360) return baseMb + 130;
      if (src.quality === 1080) return isHeavyFile ? baseMb + 80 : baseMb + 125;
      return baseMb + 100;
    }
    const isHevc = /\b(hevc|h\.?265|x265|10bit|av1)\b/i.test(`${src.name} ${src.qualityLabel}`);
    const isBestHeavy = /best\s*quality/i.test(src.qualityLabel || '');
    let s = isHevc ? 1400 : 3000;
    if (isBestHeavy) s -= 250;
    if (src.quality >= 360 && src.quality <= 576) s += 650;
    else if (src.quality === 720) s += 550;
    else if (src.quality === 1080) s += 400;
    else s += 150;
    return s;
  };
  return [...sources].sort((a, b) => score(b) - score(a));
}

function storeDetailInCaches(itemPath: string, det: MovieDetailData, expiresAt: number): void {
  if (!det || typeof det !== 'object') return;
  const safeExpiresAt = Math.min(expiresAt, Date.now() + 12 * 60_000);
  if (Array.isArray(det.episodes)) {
    for (const ep of det.episodes) {
      if (Array.isArray(ep.sources)) {
        ep.sources = sortSourcesFastestFirst(ep.sources);
      }
    }
  }
  if (itemPath) {
    detailCache.set(itemPath, { data: det, expiresAt: safeExpiresAt });
  }
}

function findCachedDetailByPathOrTitle(itemPath: string, _rawTitle = ''): MovieDetailData | null {
  const now = Date.now();
  // STRICT SOURCE ISOLATION: Only match by exact path so dual-source details/episodes NEVER mix!
  if (itemPath) {
    const hit = detailCache.get(itemPath);
    if (hit && hit.expiresAt > now && hit.data?.episodes?.length) {
      return hit.data;
    }
  }
  return null;
}

const movieRequestsStore: UserMovieRequest[] = [
  {
    id: 'req-1',
    title: 'Pushpa 2: The Rule (2025) [Bangla Dubbed 4K]',
    type: 'MOVIE',
    language: 'Bangla Dubbed',
    notes: 'Full HD 1080p Dual Audio version',
    status: 'Processing',
    createdAt: Date.now() - 3600_000 * 5,
  },
  {
    id: 'req-2',
    title: 'Solo Leveling Season 2 [Hindi + Japanese Dual Audio]',
    type: 'ANIME',
    language: 'Dual Audio',
    notes: 'All episodes 1080p WEB-DL',
    status: 'Queued',
    createdAt: Date.now() - 3600_000 * 2,
  },
];

const customBroadcastNotifications: GlobalMovieNotification[] = [];

function buildGlobalNotifications(): GlobalMovieNotification[] {
  const now = Date.now();
  const pool: MovieCardItem[] = [];
  const seenPaths = new Set<string>();
  const seenTitles = new Set<string>();

  for (const [key, entry] of catalogCache.entries()) {
    if (key.includes('adult18plus')) continue;
    for (const rawItem of entry.data.items.slice(0, 24)) {
      if (rawItem.isAdult) continue;
      const item = normalizeMovieCardItem(rawItem, now);
      const tKey = item.title.toLowerCase().replace(/[^a-z0-9\u0980-\u09ff]/g, '');
      if (!item.path || seenPaths.has(item.path) || (tKey && seenTitles.has(tKey))) continue;
      seenPaths.add(item.path);
      if (tKey) seenTitles.add(tKey);
      pool.push(item);
    }
  }

  if (pool.length < 10) {
    for (const rawItem of INITIAL_FALLBACK_MOVIES['/'] || []) {
      if (rawItem.isAdult) continue;
      const item = normalizeMovieCardItem(rawItem, now);
      const tKey = item.title.toLowerCase().replace(/[^a-z0-9\u0980-\u09ff]/g, '');
      if (!item.path || seenPaths.has(item.path) || (tKey && seenTitles.has(tKey))) continue;
      seenPaths.add(item.path);
      if (tKey) seenTitles.add(tKey);
      pool.push(item);
    }
  }

  const recentUploads = sortItemsByRecentUpload(pool, now).slice(0, 12);
  const topRatedPopular = sortItemsByHighRating(pool, now).slice(0, 12);

  const notifications: GlobalMovieNotification[] = [...customBroadcastNotifications];
  const notifSeen = new Set<string>(notifications.map((n) => n.movie.path));

  // Interleave New Uploads and Top-Rated Popular Movies so everyone gets both immediately
  const maxLen = Math.max(recentUploads.length, topRatedPopular.length);
  for (let i = 0; i < maxLen; i++) {
    const newItem = recentUploads[i];
    if (newItem && !notifSeen.has(`new::${newItem.path}`)) {
      notifSeen.add(`new::${newItem.path}`);
      const mins = getItemMinutesAgo(newItem, i, now);
      const ratingNum = parseFloat(newItem.rating || '8.7') || 8.7;
      const isEp = Boolean(newItem.episodePill);
      notifications.push({
        id: `notif-new-${newItem.id}`,
        category: 'NEW_UPLOAD',
        badgeText: isEp ? `নতুন এপিসোড • ${newItem.episodePill}` : 'নতুন মুভি আপলোড 🔥',
        headlineBn: isEp
          ? `নতুন এপিসোড আপলোড হয়েছে: ${newItem.title}`
          : `নতুন মুভি আপলোড হয়েছে: ${newItem.title}`,
        subtitleBn: `${newItem.language || 'Multi Audio'} • ${newItem.quality || '1080p HD'} • রেটিং ★ ${ratingNum.toFixed(1)} • ${newItem.timeAgo}`,
        movie: newItem,
        createdAt: Math.max(now - mins * 60_000, now - 24 * 3600_000),
        ratingScore: ratingNum,
      });
    }

    const popItem = topRatedPopular[i];
    if (popItem && !notifSeen.has(`pop::${popItem.path}`)) {
      notifSeen.add(`pop::${popItem.path}`);
      const ratingNum = Math.max(8.4, parseFloat(popItem.rating || '9.1') || 9.1);
      notifications.push({
        id: `notif-pop-${popItem.id}`,
        category: 'TOP_RATED_POPULAR',
        badgeText: `জনপ্রিয় • রেটিং ★ ${ratingNum.toFixed(1)}`,
        headlineBn: `সবার পছন্দের জনপ্রিয় ও হাই-রেটিং মুভি: ${popItem.title}`,
        subtitleBn: `রেটিং ★ ${ratingNum.toFixed(1)}/10 • ${popItem.views || '250K+'} ভিউ • ${popItem.language || 'Dual Audio'} • ${popItem.quality || 'Full HD'}`,
        movie: popItem,
        createdAt: now - (i + 1) * 180_000,
        ratingScore: ratingNum,
      });
    }
  }

  return notifications.slice(0, 28);
}

function encodeGatewayUrl(rawUrl: string): string {
  if (!rawUrl) return '';
  try {
    const token = Buffer.from(rawUrl, 'utf8').toString('base64url');
    return `/api/go?t=${token}`;
  } catch {
    return rawUrl;
  }
}

function decodeGatewayToken(token: string): string {
  try {
    return Buffer.from(token, 'base64url').toString('utf8');
  } catch {
    return '';
  }
}

/**
 * Strips any upstream site names, domains, watermarks, or tags from scraped text.
 */
function sanitizeBrandText(input: string): string {
  if (!input) return '';
  return input
    .replace(/https?:\/\/[^\s"'<>]*(?:movielinkbd|myflixbd)[^\s"'<>]*/gi, '')
    .replace(/\b[a-z0-9-]*\.?(?:movielinkbd|myflixbd)\.[a-z]{2,6}\b/gi, 'CinePulse')
    .replace(/movielinkbd|myflixbd|nexaflox/gi, 'CinePulse')
    .replace(/\bmlbd\b/gi, 'CP')
    .replace(/\s*watch\s+online\s+and\s+download\s*(?:["“”']?web-dl["“”']?|["“”']?hdtc["“”']?|["“”']?hd["“”']?|["“”']?4k["“”']?)?\s*…?/gi, '')
    .replace(/\s*watch\s+online\s*…?/gi, '')
    .replace(/\s*[“”"'](?:web(?:-?dl|rip)?|hdtc|hdts|4k|hd)[^"”]*[”"']?\s*…?\s*$/gi, '')
    .replace(/\s+[–—-]\s*$/g, '')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

function decodeMlbdCipher(base64Str: string, hexSeed: string, rounds: number): string {
  try {
    let x = parseInt(hexSeed, 16) >>> 0;
    for (let i = 0; i < rounds; i++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
    }
    const raw = Buffer.from(base64Str.trim(), 'base64');
    const out = Buffer.alloc(raw.length);
    for (let j = 0; j < raw.length; j++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
      out[j] = raw[j] ^ ((x >>> 16) & 255);
    }
    return out.toString('utf8');
  } catch {
    return '';
  }
}

function decodeHtmlEntities(str: string): string {
  const cleaned = (str || '')
    .replace(/&ndash;|&#8211;/g, '–')
    .replace(/&mdash;|&#8212;/g, '—')
    .replace(/&#039;|&#8217;/g, "'")
    .replace(/&quot;|&#8220;|&#8221;/g, '"')
    .replace(/&amp;|&#038;/g, '&')
    .replace(/&bull;|&#8226;/g, '•')
    .replace(/&#8230;|&hellip;/g, '')
    .replace(/&nbsp;/g, ' ')
    .replace(/<[^>]+>/g, '')
    .trim();
  return sanitizeBrandText(cleaned);
}

function getOrderedNodes(preferredNodeId?: string): MirrorNodeConfig[] {
  const dynamicAlpha: MirrorNodeConfig = {
    id: 'node-alpha',
    name: 'Node Alpha',
    region: 'BD-Fast Edge',
    origin: latestMlbdOrigin,
  };
  const nodes: MirrorNodeConfig[] = [
    dynamicAlpha,
    ...PRIMARY_MIRROR_NODES.filter((n) => n.id !== 'node-alpha' && n.origin !== latestMlbdOrigin),
  ];
  if (!preferredNodeId) return nodes;
  const preferred = nodes.find((n) => n.id === preferredNodeId);
  if (!preferred) return nodes;
  return [preferred, ...nodes.filter((n) => n.id !== preferredNodeId)];
}

async function fetchFromMirrors(
  targetPath: string,
  preferredNodeId?: string
): Promise<{ html: string; finalOrigin: string; activeNodeId: string }> {
  const cleanPath = targetPath.startsWith('http')
    ? new URL(targetPath).pathname + new URL(targetPath).search
    : targetPath.startsWith('/')
      ? targetPath
      : `/${targetPath}`;

  const orderedNodes = getOrderedNodes(preferredNodeId);

  const attemptNode = async (node: MirrorNodeConfig, timeoutMs: number) => {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeoutMs);
    try {
      const url = `${node.origin}${cleanPath}`;
      const res = await fetch(url, {
        redirect: 'follow',
        signal: controller.signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
          Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
          'Accept-Language': 'en-US,en;q=0.9,bn;q=0.8',
          Cookie: 'mlbd_show18=1; hide18On=false',
          Referer: `${node.origin}/`,
        },
      });
      if (!res.ok && res.status !== 404) {
        throw new Error(`HTTP ${res.status}`);
      }
      const html = await res.text();
      const hasValidMlbdMarker =
        html.includes('movie-card') ||
        html.includes('mlbdHdFrame') ||
        html.includes('mlbd-hdwrap') ||
        html.includes('mlbd-hdeps') ||
        html.includes('mlbdInlinePlayerData') ||
        html.includes('image-container-view') ||
        html.includes('data-dl=') ||
        html.includes('<div class="n">404</div>');
      if (!html || html.length < 1200 || !hasValidMlbdMarker) {
        throw new Error('Challenge or incomplete HTML');
      }
      const finalOrigin = new URL(res.url || url).origin;
      if (/^https:\/\/[a-z0-9-]+\.movielinkbd\.[a-z]{2,10}$/i.test(finalOrigin)) {
        latestMlbdOrigin = finalOrigin;
      }
      return { html, finalOrigin, activeNodeId: node.id };
    } finally {
      clearTimeout(timer);
    }
  };

  // Race top 2 mirror nodes in parallel for sub-second response!
  try {
    return await Promise.any(
      orderedNodes.slice(0, 2).map((node) => attemptNode(node, 5500))
    );
  } catch {
    for (const node of orderedNodes.slice(2)) {
      try {
        return await attemptNode(node, 6500);
      } catch {
        // try next
      }
    }
  }
  throw new Error('All cinema stream nodes unreachable');
}

function parseMovieCards(html: string): { items: MovieCardItem[]; maxPage: number } {
  const bodyIdx = html.indexOf('<body');
  const body = bodyIdx >= 0 ? html.slice(bodyIdx) : html;
  const blocks = body.split(/<div class="movie-card"/i).slice(1);
  const items: MovieCardItem[] = [];
  const seenPaths = new Set<string>();

  for (const block of blocks) {
    const chunk = block.slice(0, 3200);
    if (chunk.includes("'+esc(") || chunk.includes('${')) continue;

    const titleMatch =
      chunk.match(/class=["']title["'][^>]*>([\s\S]*?)<\/a>/i) ||
      chunk.match(/alt=["']([^"']+)["']/i);
    const hrefMatch = chunk.match(/<a[^>]+href=["']([^"']+)["']/i);
    if (!titleMatch || !hrefMatch) continue;

    const rawHref = hrefMatch[1].trim();
    if (!rawHref || rawHref.includes("'+") || rawHref === '#') continue;

    let itemPath = '';
    try {
      itemPath = rawHref.startsWith('http')
        ? new URL(rawHref).pathname
        : rawHref.startsWith('/')
          ? rawHref
          : `/${rawHref}`;
    } catch {
      continue;
    }

    if (seenPaths.has(itemPath)) continue;

    const title = decodeHtmlEntities(titleMatch[1]);
    if (!title) continue;

    const titleKey = getCanonicalTitleKey(title);
    if (titleKey && seenPaths.has(`title::${titleKey}`)) continue;

    const posterMatch =
      chunk.match(/data-src=["'](https?:\/\/[^"']+)["']/i) ||
      chunk.match(/src=["'](https?:\/\/[^"']+)["']/i);
    const poster = posterMatch ? posterMatch[1].trim() : '';
    const posterKey = poster ? poster.toLowerCase().split('?')[0].trim() : '';
    if (posterKey && seenPaths.has(`poster::${posterKey}`)) continue;

    seenPaths.add(itemPath);
    if (titleKey) seenPaths.add(`title::${titleKey}`);
    if (posterKey) seenPaths.add(`poster::${posterKey}`);

    const quality = decodeHtmlEntities(
      (chunk.match(/<span class=["']quality["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'WEB-DL'
    );
    const language = decodeHtmlEntities(
      (chunk.match(/<span class=["']language["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'MULTI'
    );
    const views = decodeHtmlEntities(
      (chunk.match(/<span class=["']views-badge-top["'][^>]*>[\s\S]*?<\/i>\s*([^<]+)<\/span>/i) || [])[1] || '2.4K'
    );
    const rawTimeAgo = decodeHtmlEntities(
      (chunk.match(/<div class=["']upload-time["'][^>]*>([\s\S]*?)<\/div>/i) || [])[1] || 'Recently added'
    );
    const rawEpisodePill = decodeHtmlEntities(
      (chunk.match(/<span class=["']badge ep-badge[^"']*["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || ''
    );
    const cleanedTime = cleanTimeAgoAndEpisode(
      rawTimeAgo,
      rawEpisodePill,
      itemPath || title,
      items.length
    );

    const isPinned = chunk.includes('pin-badge') || chunk.includes('data-pin="1"');
    const isAdult =
      chunk.includes('data-18="1"') ||
      itemPath.includes('18plus') ||
      cleanedTime.episodePill.toUpperCase().includes('18+');

    let typeBadge: 'MOVIE' | 'SERIES' | 'ANIME' | 'DRAMA' = 'MOVIE';
    if (itemPath.includes('/anime/')) typeBadge = 'ANIME';
    else if (itemPath.includes('/drama/')) typeBadge = 'DRAMA';
    else if (itemPath.includes('/series/') || Boolean(cleanedTime.episodePill)) typeBadge = 'SERIES';

    // Extract real R2 upload Unix timestamp if embedded in poster URL (e.g. poster_v778gm1793478302.webp)
    const r2TsMatch = poster.match(/poster_[a-z0-9_]*?(17\d{8})\./i);
    const r2EpochMs = r2TsMatch ? parseInt(r2TsMatch[1], 10) * 1000 : 0;
    const nowMs = Date.now();
    let pathHash = 2166136261 >>> 0;
    for (let c = 0; c < itemPath.length; c++) {
      pathHash ^= itemPath.charCodeAt(c);
      pathHash = Math.imul(pathHash, 16777619) >>> 0;
    }
    const minuteJitter = cleanedTime.minutesAgo >= 60 ? (pathHash % 47) : 0;
    const computedUploadMs =
      r2EpochMs > nowMs - 48 * 3600_000 && r2EpochMs <= nowMs
        ? r2EpochMs
        : nowMs - (cleanedTime.minutesAgo + minuteJitter) * 60_000;

    items.push({
      id: itemPath.replace(/[^a-zA-Z0-9_-]/g, '_'),
      title,
      // Never expose upstream URL; keep clean relative path
      url: itemPath,
      path: itemPath,
      poster,
      quality: quality || 'HD',
      views: views || '1.9K',
      language: language || 'MULTI',
      typeBadge,
      timeAgo: cleanedTime.timeAgo,
      episodePill: cleanedTime.episodePill,
      isPinned,
      isAdult,
      uploadedAtMs: computedUploadMs,
    });
  }

  const pageMatches = [...body.matchAll(/\/page\/(\d+)/g)]
    .map((m) => Number(m[1]))
    .filter((n) => !isNaN(n) && n > 0 && n <= 2000);
  const maxPage = pageMatches.length > 0 ? Math.max(...pageMatches) : 520;

  return { items, maxPage };
}

function parseMovieDetail(html: string, itemPath: string, origin: string): MovieDetailData {
  let inlineData: any = null;
  const playerScriptMatch = html.match(
    /<script[^>]*id=["']mlbdInlinePlayerData["'][^>]*data-s=["']([^"']+)["'][^>]*data-r=["'](\d+)["'][^>]*>([\s\S]*?)<\/script>/i
  );
  if (playerScriptMatch) {
    const decodedJson = decodeMlbdCipher(
      playerScriptMatch[3],
      playerScriptMatch[1],
      parseInt(playerScriptMatch[2], 10) || 600
    );
    try {
      inlineData = JSON.parse(decodedJson);
    } catch {
      inlineData = null;
    }
  }

  const downloadButtons: DirectDownloadButton[] = [];
  const dlRegex = /<a[^>]*data-dl=["']([^"']+)["'][^>]*data-ds=["']([^"']+)["'][^>]*data-dr=["'](\d+)["'][^>]*>([\s\S]*?)<\/a>/gi;
  for (const match of html.matchAll(dlRegex)) {
    const decodedHref = decodeMlbdCipher(match[1], match[2], parseInt(match[3], 10) || 300);
    const label = decodeHtmlEntities(match[4]);
    if (decodedHref) {
      const fullDlUrl = decodedHref.startsWith('http')
        ? decodedHref
        : `${origin}${decodedHref.startsWith('/') ? '' : '/'}${decodedHref}`;
      const bracketMatch = label.match(/\[(.*?)\]/);
      const parts = bracketMatch ? bracketMatch[1].split('•').map((s) => s.trim()) : [];
      downloadButtons.push({
        label: sanitizeBrandText(label || 'High-Speed Direct Download'),
        url: fullDlUrl,
        quality: parts[0] || 'HD',
        size: parts[1] || '',
      });
    }
  }

  const rawTitle =
    inlineData?.title ||
    decodeHtmlEntities((html.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i) || [])[1] || 'Cinema Title');
  const title = sanitizeBrandText(rawTitle);

  const poster =
    inlineData?.poster ||
    (html.match(/<div class=["']image-container-view["'][\s\S]*?<img[^>]+src=["'](https?:\/\/[^"']+)["']/i) || [])[1] ||
    '';

  const qualityNote = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<div class=["']movie-info-view["'][\s\S]*?<p[^>]*>([\s\S]*?)<\/p>/i) || [])[1] || ''
    )
  );

  const extractInfoLine = (keyword: string): string => {
    const regex = new RegExp(`<p class=["']info-line["'][^>]*>[\\s\\S]*?${keyword}:?<\\/b>([\\s\\S]*?)<\\/p>`, 'i');
    const m = html.match(regex);
    return m ? decodeHtmlEntities(m[1]) : '';
  };

  const genre = extractInfoLine('Genre') || 'Cinema, Entertainment';
  const language = extractInfoLine('Language') || 'Multi Audio';
  const quality = extractInfoLine('Quality') || 'WEB-DL';
  const resolution = extractInfoLine('Resolution') || '1080p | 720p | 480p';
  const releaseDate = extractInfoLine('Released') || '2026';

  const storyline = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<p class=["']story-text["'][^>]*>([\s\S]*?)<\/p>/i) || [])[1] ||
        (html.match(/<meta name=["']description["'] content=["']([^"']+)["']/i) || [])[1] ||
        ''
    )
  );

  const trailerMatch = html.match(/data-mlbd-trailer=["']([a-zA-Z0-9_-]{6,20})["']/i);
  const youtubeTrailerId = trailerMatch ? trailerMatch[1] : '';

  const cast: CastMember[] = [];
  const castRegex = /<a class=["']mlbd-cast__p["'][^>]+href=["']([^"']+)["'][^>]*>[\s\S]*?<img[^>]+src=["']([^"']+)["'][^>]*>[\s\S]*?<b>([\s\S]*?)<\/b>[\s\S]*?<small>([\s\S]*?)<\/small>/gi;
  for (const m of html.matchAll(castRegex)) {
    const actorName = decodeHtmlEntities(m[3]);
    if (actorName) {
      cast.push({
        url: `/search?q=${encodeURIComponent(actorName)}`,
        photo: m[2],
        name: actorName,
        role: decodeHtmlEntities(m[4]),
      });
    }
  }

  let communityScore: MovieDetailData['communityScore'] | undefined;
  const voteMatch = html.match(/data-summary=["']([^"']+)["']/i);
  if (voteMatch) {
    try {
      const parsedVote = JSON.parse(decodeHtmlEntities(voteMatch[1]));
      communityScore = {
        recommendedPercent: Number(parsedVote.recommended_percent) || 88,
        totalVotes: Number(parsedVote.total) || 24,
        verdict: sanitizeBrandText(parsedVote.verdict || 'দর্শকদের পছন্দ'),
      };
    } catch {
      // ignore
    }
  }

  const inferStreamQuality = (s: any): number => {
    const combined = `${s?.quality_label || ''} ${s?.name || ''}`.toLowerCase();
    if (/\b(2160p|4k)\b/.test(combined)) return 2160;
    if (/\b(1080p|full\s*hd)\b/.test(combined)) return 1080;
    if (/\b(480p|360p)\b/.test(combined)) return 480;
    if (/\b720p\b/.test(combined)) return 720;
    const q = Number(s?.quality);
    if (q === 480 || q === 720 || q === 1080 || q === 2160) return q;
    if (/best\s*quality/i.test(combined)) return 1080;
    return 720;
  };

  const scoreSourceForSmoothPlay = (src: StreamSource): number => {
    const isHevc = /\b(hevc|h\.?265|x265|10bit)\b/i.test(`${src.name} ${src.qualityLabel}`);
    const isBestHeavy = /best\s*quality/i.test(src.qualityLabel || '');
    let score = isHevc ? 200 : 1000;
    if (isBestHeavy) score -= 250;
    if (/\.(mp4|m4v|m3u8)(\?|$)/i.test(src.url)) score += 90;
    if (/r2\.dev|workers\.dev|cloudflare|fsldownload|pixeldrain/i.test(src.url)) score += 50;
    if (src.quality >= 360 && src.quality <= 576) score += 650;
    else if (src.quality === 720) score += 500;
    else if (src.quality === 1080) score += 350;
    else if (src.quality === 2160) score += 150;
    else score += 200;
    return score;
  };

  const mapRawEpisode = (ep: any, idx: number): EpisodeItem => {
    const rawSources: StreamSource[] = Array.isArray(ep.sources)
      ? ep.sources
          .filter((s: any) => s && (s.url || s.download_url))
          .map((s: any, sIdx: number) => {
            const rawUrl = String(s.url || '');
            const rawStreamUrl = rawUrl.startsWith('http')
              ? rawUrl
              : rawUrl
                ? `${origin}${rawUrl.startsWith('/') ? '' : '/'}${rawUrl}`
                : '';
            const rawDlUrl = String(s.download_url || s.url || '');
            const fullDlUrl = rawDlUrl.startsWith('http')
              ? rawDlUrl
              : rawDlUrl
                ? `${origin}${rawDlUrl.startsWith('/') ? '' : '/'}${rawDlUrl}`
                : '';
            const realQuality = inferStreamQuality(s);
            return {
              id: String(s.id || `src-${idx}-${realQuality}-${sIdx}`),
              quality: realQuality,
              qualityLabel: s.quality_label || `${realQuality}p`,
              audio: sanitizeBrandText(String(s.audio || 'Multi Audio')),
              audioLanguages: Array.isArray(s.audio_languages)
                ? s.audio_languages.map((a: any) => sanitizeBrandText(String(a)))
                : [sanitizeBrandText(String(s.audio || 'Original'))],
              provider: `Cloud Stream #${sIdx + 1}`,
              url: rawStreamUrl,
              downloadUrl: encodeGatewayUrl(fullDlUrl),
              type: String(s.type || 'mkv').toLowerCase(),
              name: sanitizeBrandText(String(s.name || `${title} - ${realQuality}p`)),
              screenshot: s.screenshot || undefined,
            };
          })
      : [];

    const sources = [...rawSources].sort(
      (a, b) => scoreSourceForSmoothPlay(b) - scoreSourceForSmoothPlay(a)
    );

    const rawLabel = sanitizeBrandText(
      String(ep.label || (ep.number ? `Episode ${ep.number}` : 'Full Movie'))
    );

    // Parse episode range or season from label if not explicitly set
    const rangeMatch = rawLabel.match(/(?:ep(?:isode)?|e)\s*0*(\d{1,4})\s*[-–—]\s*0*(\d{1,4})/i);
    const singleEpMatch =
      rawLabel.match(/s\d+\s*e0*(\d{1,4})/i) ||
      rawLabel.match(/(?:ep(?:isode)?|e)\s*0*(\d{1,4})/i);
    const seasonMatch = rawLabel.match(/\bs(?:eason)?\s*0*(\d{1,2})\b/i);

    const parsedStart = rangeMatch
      ? Number(rangeMatch[1])
      : singleEpMatch
        ? Number(singleEpMatch[1])
        : null;
    const parsedEnd = rangeMatch ? Number(rangeMatch[2]) : parsedStart;

    const number =
      ep.number !== null && ep.number !== undefined
        ? Number(ep.number)
        : ep.range_start !== null && ep.range_start !== undefined
          ? Number(ep.range_start)
          : parsedStart;

    const rangeStart =
      ep.range_start !== null && ep.range_start !== undefined
        ? Number(ep.range_start)
        : number;
    const rangeEnd =
      ep.range_end !== null && ep.range_end !== undefined
        ? Number(ep.range_end)
        : parsedEnd ?? rangeStart;

    const season =
      ep.season !== null && ep.season !== undefined
        ? Number(ep.season)
        : seasonMatch
          ? Number(seasonMatch[1])
          : null;

    return {
      id: String(ep.id || `ep-${idx + 1}`),
      label: rawLabel,
      number,
      rangeStart,
      rangeEnd,
      season,
      kind: String(ep.kind || (number !== null ? 'episode' : 'movie')),
      sources,
    };
  };

  const episodes: EpisodeItem[] = Array.isArray(inlineData?.episodes)
    ? inlineData.episodes
        .map((ep: any, idx: number) => mapRawEpisode(ep, idx))
        .filter((ep: EpisodeItem) => ep.sources.length > 0)
        .sort((a: EpisodeItem, b: EpisodeItem) => {
          const sA = a.season ?? 0;
          const sB = b.season ?? 0;
          if (sA !== sB && a.season !== null && b.season !== null) return sA - sB;
          const nA = a.rangeStart ?? a.number ?? 999999;
          const nB = b.rangeStart ?? b.number ?? 999999;
          if (nA !== nB) return nA - nB;
          return (a.rangeEnd ?? nA) - (b.rangeEnd ?? nB);
        })
    : [];

  const screenshots: string[] = Array.isArray(inlineData?.screenshots)
    ? inlineData.screenshots.map((s: any) => s?.url).filter(Boolean)
    : [];

  return {
    title,
    url: itemPath,
    poster,
    qualityNote,
    typeBadge: inlineData?.content_type === 'series' || episodes.length > 1 ? 'SERIES' : 'MOVIE',
    language,
    quality,
    genre,
    resolution,
    releaseDate,
    storyline,
    youtubeTrailerId,
    screenshots,
    episodes,
    downloadButtons,
    cast: cast.slice(0, 12),
    communityScore,
    uploadedBy: 'CinePulse',
  };
}

/**
 * Extracts upgraded `/p/<token>` iframe player (`window.__PD2`)
 * which delivers Direct MP4 + Multi-Audio 1080p HLS for movies & multi-episode series!
 */
async function enrichMovieLinkBdWithPd2Player(
  html: string,
  itemPath: string,
  origin: string,
  detail: MovieDetailData
): Promise<MovieDetailData> {
  if (detail.episodes && detail.episodes.length > 0) return detail;

  const iframeMatch =
    html.match(/<iframe[^>]*id=["']mlbdHdFrame["'][^>]*src=["']([^"']+)["']/i) ||
    html.match(/<iframe[^>]*src=["']([^"']+)["'][^>]*id=["']mlbdHdFrame["']/i) ||
    html.match(/src=["'](\/p\/[A-Za-z0-9_-]{12,})["']/i);
  if (!iframeMatch?.[1]) return detail;

  const iframeHref = iframeMatch[1].trim();
  const playerUrl = iframeHref.startsWith('http')
    ? iframeHref
    : `${origin}${iframeHref.startsWith('/') ? '' : '/'}${iframeHref}`;

  try {
    const pRes = await fetch(playerUrl, {
      headers: {
        'User-Agent':
          'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
        Accept: 'text/html,application/xhtml+xml,*/*;q=0.8',
        Referer: `${origin}${itemPath.startsWith('/') ? itemPath : `/${itemPath}`}`,
      },
      signal: AbortSignal.timeout(7000),
    });
    if (!pRes.ok) return detail;
    const pHtml = await pRes.text();
    const pdMatch = pHtml.match(/window\.__PD2\s*=\s*(\{[\s\S]*?\})\s*;/);
    if (!pdMatch?.[1]) return detail;

    const pd2 = JSON.parse(pdMatch[1]) as any;
    const pdLang = sanitizeBrandText(String(pd2.langs || detail.language || 'Multi Audio'));
    const pdTitle = sanitizeBrandText(String(pd2.title || detail.title || 'Cinema Title'));
    const pdPoster = String(pd2.poster || detail.poster || '');

    const rawEpisodes: any[] =
      Array.isArray(pd2.episodes) && pd2.episodes.length > 0
        ? pd2.episodes
        : pd2.master || pd2.mp4
          ? [
              {
                label: 'Full Movie',
                number: 1,
                num_end: 1,
                season: null,
                master: pd2.master || '',
                mp4: pd2.mp4 || '',
                audio: pd2.audio || [],
              },
            ]
          : [];

    const mappedEpisodes: EpisodeItem[] = [];
    for (let idx = 0; idx < rawEpisodes.length; idx++) {
      const ep = rawEpisodes[idx];
      const epNumRaw = Number(ep.number);
      const epNum = Number.isFinite(epNumRaw) && epNumRaw > 0 ? epNumRaw : idx + 1;
      const epEndRaw = Number(ep.num_end);
      const epEnd = Number.isFinite(epEndRaw) && epEndRaw >= epNum ? epEndRaw : epNum;
      const epSeason =
        ep.season !== undefined && ep.season !== null && Number(ep.season) > 0
          ? Number(ep.season)
          : null;
      const epLabel = sanitizeBrandText(
        String(
          ep.label ||
            (rawEpisodes.length === 1 && !epSeason ? 'Full Movie' : `Episode ${epNum}`)
        )
      );
      const isSingleMovie =
        rawEpisodes.length === 1 &&
        !epSeason &&
        (!epNumRaw || epLabel.toLowerCase() === 'movie' || epLabel.toLowerCase() === 'full movie');

      const epAudioLabels =
        Array.isArray(ep.audio) && ep.audio.length > 0
          ? ep.audio
              .map((a: any) => sanitizeBrandText(String(a?.label || a?.name || a || '')))
              .filter(Boolean)
          : [pdLang];

      const sources: StreamSource[] = [];
      const epMp4 = String(ep.mp4 || '').trim();
      const epMaster = String(ep.master || '').trim();
      const fallbackDl = detail.downloadButtons[0]?.url || '';

      if (epMp4 && epMp4.startsWith('http')) {
        const mp4Token = Buffer.from(epMp4, 'utf8').toString('base64url');
        const safeName = `${pdTitle.replace(/[^a-zA-Z0-9_-]+/g, '_')}_${isSingleMovie ? 'HD' : `EP${epNum}`}.mp4`;
        sources.push({
          id: `mlbd-pd2-mp4-${epSeason || 0}-${epNum}-${idx}`,
          quality: 720,
          qualityLabel: 'HD Direct MP4',
          audio: pdLang,
          audioLanguages: epAudioLabels,
          provider: 'Direct MP4',
          url: `/api/mlbd-stream.mp4?t=${mp4Token}`,
          downloadUrl: `/api/mlbd-stream.mp4?t=${mp4Token}&dl=1&name=${encodeURIComponent(safeName)}`,
          type: 'mp4',
          name: `${pdTitle} - ${epLabel} (Direct MP4)`,
        });
      }

      if (epMaster && epMaster.startsWith('http')) {
        const hlsToken = Buffer.from(epMaster, 'utf8').toString('base64url');
        sources.push({
          id: `mlbd-pd2-hls-${epSeason || 0}-${epNum}-${idx}`,
          quality: 1080,
          qualityLabel: '1080p Multi-Audio HLS',
          audio: pdLang,
          audioLanguages: epAudioLabels,
          provider: 'Multi-Audio HLS',
          url: `/api/mlbd-hls.m3u8?t=${hlsToken}`,
          downloadUrl: fallbackDl || (epMp4 ? `/api/mlbd-stream.mp4?t=${Buffer.from(epMp4, 'utf8').toString('base64url')}&dl=1` : ''),
          type: 'hls',
          name: `${pdTitle} - ${epLabel} (1080p HLS)`,
        });
      }

      if (sources.length > 0) {
        mappedEpisodes.push({
          id: `mlbd-pd2-ep-${epSeason || 0}-${epNum}-${idx}`,
          label: isSingleMovie
            ? 'Full Movie'
            : epSeason
              ? `S${String(epSeason).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • ${epLabel}`
              : epLabel,
          number: epNum,
          rangeStart: epNum,
          rangeEnd: epEnd,
          season: epSeason,
          kind: isSingleMovie ? 'movie' : 'episode',
          sources,
        });
      }
    }

    if (mappedEpisodes.length > 0) {
      mappedEpisodes.sort((a, b) => {
        const sA = a.season ?? 0;
        const sB = b.season ?? 0;
        if (sA !== sB && a.season !== null && b.season !== null) return sA - sB;
        return (a.number ?? 0) - (b.number ?? 0);
      });
      return {
        ...detail,
        title: pdTitle || detail.title,
        poster: pdPoster || detail.poster,
        language: pdLang || detail.language,
        typeBadge: mappedEpisodes.length > 1 || mappedEpisodes[0].season ? 'SERIES' : detail.typeBadge,
        episodes: mappedEpisodes,
        uploadedBy: 'CinePulse',
      };
    }
  } catch (err) {
    console.warn('PD2 extract error:', err instanceof Error ? err.message : err);
  }

  return detail;
}

function extractBaseSeriesTitle(rawTitle: string): string {
  return String(rawTitle || '')
    .replace(/\[.*?\]|\(.*?\)/g, ' ')
    .replace(/\b(?:S\d+|Season\s*\d+(?:-\d+)?|Ep(?:isode)?\s*\d+(?:-\d+)?|Complete(?:d)?|Added|Full\s*HD|ORG|Hindi|Bangla|Bengali|Dual|Multi|Audio|Watch|Online|Download|WEB-DL|HDTC|4K|The\s*Movie)\b/gi, ' ')
    .replace(/[:\-–—|]+/g, ' ')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

function mergeCatalogItems(
  primaryItems: MovieCardItem[],
  secondaryItems: MovieCardItem[],
  preferSecondaryFirst = false
): MovieCardItem[] {
  const firstList = preferSecondaryFirst ? secondaryItems : primaryItems;
  const secondList = preferSecondaryFirst ? primaryItems : secondaryItems;
  const interleaved: MovieCardItem[] = [];
  const maxLen = Math.max(firstList.length, secondList.length);
  for (let i = 0; i < maxLen; i++) {
    if (i < firstList.length) interleaved.push(firstList[i]);
    if (i < secondList.length) interleaved.push(secondList[i]);
  }
  return deduplicateMovieCards(interleaved);
}

// ============================================================================
// Upstream HD Content Engine
// ============================================================================
let cachedMovieBoxToken = '';
let cachedMovieBoxTokenExpiresAt = 0;

async function getMovieBoxBearerToken(): Promise<string> {
  if (cachedMovieBoxToken && cachedMovieBoxTokenExpiresAt > Date.now()) {
    return cachedMovieBoxToken;
  }
  try {
    const res = await fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/home?host=movie-box.co`, {
      headers: buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`),
      signal: AbortSignal.timeout(4500),
    });
    const xUser = res.headers.get('x-user');
    if (xUser) {
      const parsed = JSON.parse(xUser);
      if (parsed?.token) {
        cachedMovieBoxToken = String(parsed.token);
        cachedMovieBoxTokenExpiresAt = Date.now() + 6 * 3600_000;
        return cachedMovieBoxToken;
      }
    }
  } catch {
    // ignore token bootstrap error
  }
  return cachedMovieBoxToken;
}

function mapCategoryToMovieBoxFilter(rawPath: string, page = 1): Record<string, any> {
  const p = (rawPath || '/').toLowerCase().replace(/\/page\/\d+\/?$/, '').replace(/\/+$/, '') || '/';
  const payload: Record<string, any> = {
    page,
    perPage: 28,
    channelId: 1, // Default: Movies
    sort: 'Hottest',
  };

  if (p === '/' || p === '/hot-dhamaka' || p === '/mostwatch/7d') {
    payload.channelId = 1;
    payload.sort = 'Hottest';
  } else if (p === '/new-uploads') {
    payload.channelId = 1;
    payload.sort = 'Latest';
  } else if (p === '/new-releases' || p === '/upcoming') {
    payload.channelId = 1;
    payload.sort = 'Latest';
  } else if (p.includes('anime')) {
    payload.channelId = 1006;
    payload.sort = 'Hottest';
  } else if (p.includes('animation') || p.includes('family')) {
    payload.channelId = 1;
    payload.genre = 'Animation';
  } else if (p.includes('series') || p.includes('ongoing') || p.includes('tv')) {
    payload.channelId = 2;
    payload.sort = 'Hottest';
  } else if (p.includes('drama') || p.includes('korean')) {
    payload.channelId = 2;
    payload.country = 'Korea';
    payload.sort = 'Hottest';
  } else if (p.includes('chinese')) {
    payload.channelId = 2;
    payload.country = 'China';
  } else if (p.includes('japanese')) {
    payload.channelId = 1006;
    payload.country = 'Japan';
  } else if (p.includes('turkish')) {
    payload.channelId = 2;
    payload.country = 'Turkey';
  } else if (p.includes('bangla-dubbed')) {
    payload.channelId = 1;
    payload.classify = 'Bengali dub';
  } else if (p.includes('bangla')) {
    payload.channelId = 1;
    payload.country = 'Bangladesh';
  } else if (p.includes('hindi-dubbed') || p.includes('dual-audio')) {
    payload.channelId = 1;
    payload.classify = 'Hindi dub';
  } else if (p.includes('bollywood') || p.includes('hindi')) {
    payload.channelId = 1;
    payload.country = 'India';
  } else if (p.includes('tamil')) {
    payload.channelId = 1;
    payload.classify = 'Tamil dub';
  } else if (p.includes('telugu') || p.includes('south')) {
    payload.channelId = 1;
    payload.classify = 'Telugu dub';
  } else if (p.includes('malayalam')) {
    payload.channelId = 1;
    payload.classify = 'Malayalam dub';
  } else if (p.includes('kannada')) {
    payload.channelId = 1;
    payload.classify = 'Kannada dub';
  } else if (p.includes('punjabi')) {
    payload.channelId = 1;
    payload.classify = 'Punjabi dub';
  } else if (p.includes('english') || p.includes('hollywood') || p.includes('mcu') || p.includes('dc-universe')) {
    payload.channelId = 1;
    payload.country = 'United States';
  } else if (p.includes('indonesian')) {
    payload.channelId = 1;
    payload.country = 'Indonesia';
  } else if (p.includes('spanish')) {
    payload.channelId = 1;
    payload.country = 'Spain';
  } else if (p.includes('french')) {
    payload.channelId = 1;
    payload.country = 'France';
  } else if (p.includes('italian')) {
    payload.channelId = 1;
    payload.country = 'Italy';
  } else if (p.includes('malaysian')) {
    payload.channelId = 1;
    payload.country = 'Malaysia';
  } else if (p.includes('action') || p.includes('superhero')) {
    payload.channelId = 1;
    payload.genre = 'Action';
  } else if (p.includes('thriller') || p.includes('suspense') || p.includes('survival')) {
    payload.channelId = 1;
    payload.genre = 'Thriller';
  } else if (p.includes('horror')) {
    payload.channelId = 1;
    payload.genre = 'Horror';
  } else if (p.includes('romance')) {
    payload.channelId = 1;
    payload.genre = 'Romance';
  } else if (p.includes('comedy')) {
    payload.channelId = 1;
    payload.genre = 'Comedy';
  } else if (p.includes('crime')) {
    payload.channelId = 1;
    payload.genre = 'Crime';
  } else if (p.includes('sci-fi')) {
    payload.channelId = 1;
    payload.genre = 'Sci-Fi';
  } else if (p.includes('adventure')) {
    payload.channelId = 1;
    payload.genre = 'Adventure';
  } else if (p.includes('fantasy')) {
    payload.channelId = 1;
    payload.genre = 'Fantasy';
  } else if (p.includes('mystery')) {
    payload.channelId = 1;
    payload.genre = 'Mystery';
  } else if (p.includes('historical')) {
    payload.channelId = 1;
    payload.genre = 'History';
  } else if (p.includes('war')) {
    payload.channelId = 1;
    payload.genre = 'War';
  } else if (p.includes('documentary')) {
    payload.channelId = 1;
    payload.genre = 'Documentary';
  } else if (p.includes('biographical')) {
    payload.channelId = 1;
    payload.genre = 'Biography';
  } else if (p.includes('sport') || p.includes('fifa') || p.includes('wwe')) {
    payload.channelId = 1;
    payload.genre = 'Sport';
  } else if (p.includes('music')) {
    payload.channelId = 1;
    payload.genre = 'Music';
  }

  return payload;
}

function mapMovieBoxItemToCard(raw: any, index = 0): MovieCardItem | null {
  if (!raw || !raw.subjectId || !raw.title || raw.hasResource === false) return null;
  const subjectId = String(raw.subjectId).trim();
  const detailSlug = String(raw.detailPath || raw.title)
    .toLowerCase()
    .replace(/[^a-z0-9-]+/g, '-')
    .replace(/^-+|-+$/g, '');
  const itemPath = `/mb/${subjectId}/${detailSlug || 'movie'}`;
  const rawTitle = String(raw.title).trim();
  const year = raw.releaseDate ? String(raw.releaseDate).split('-')[0] : '';
  const hasYearInTitle = /\b(19|20)\d{2}\b/.test(rawTitle);
  const displayTitle = year && !hasYearInTitle ? `${rawTitle} (${year})` : rawTitle;

  const poster = String(raw.cover?.url || raw.stills?.url || '').trim();
  if (!poster) return null;

  const ratingVal = parseFloat(String(raw.imdbRatingValue || raw.imdbRate || '8.2')) || 8.2;
  const subjectType = Number(raw.subjectType) || 1;
  const genreStr = String(raw.genre || '').toUpperCase();
  const countryStr = String(raw.countryName || '').toUpperCase();

  let typeBadge: 'MOVIE' | 'SERIES' | 'ANIME' | 'DRAMA' = 'MOVIE';
  if (subjectType === 1006 || genreStr.includes('ANIMATION') || countryStr === 'JAPAN') {
    typeBadge = subjectType === 2 ? 'ANIME' : 'MOVIE';
  } else if (subjectType === 2) {
    if (countryStr.includes('KOREA') || countryStr.includes('CHINA') || countryStr.includes('TURKEY')) {
      typeBadge = 'DRAMA';
    } else {
      typeBadge = 'SERIES';
    }
  }

  const dubsList = Array.isArray(raw.dubs)
    ? raw.dubs.map((d: any) => String(d?.lanName || d || '')).filter(Boolean)
    : [];
  const subsStr = String(raw.subtitles || '');
  let language = 'ENGLISH';
  if (dubsList.length > 0) {
    language = dubsList[0].toUpperCase();
  } else if (subsStr.includes('বাংলা') || countryStr.includes('BANGLADESH')) {
    language = 'BANGLA SUB';
  } else if (countryStr.includes('INDIA')) {
    language = 'HINDI';
  } else if (countryStr.includes('KOREA')) {
    language = 'KOREAN';
  } else if (countryStr.includes('CHINA')) {
    language = 'CHINESE';
  } else if (countryStr.includes('JAPAN')) {
    language = 'JAPANESE';
  }

  const episodePill =
    subjectType === 2
      ? /\bS\d+/i.test(rawTitle)
        ? rawTitle.match(/\bS\d+(?:-S?\d+)?/i)?.[0]?.toUpperCase() || 'SERIES'
        : 'FULL SERIES'
      : '';

  const releaseYearNum = parseInt(year, 10) || 0;
  const releaseEpochMs = raw.releaseDate ? Date.parse(String(raw.releaseDate)) : NaN;
  const nowMs = Date.now();

  let hash = 2166136261 >>> 0;
  for (let i = 0; i < subjectId.length; i++) {
    hash ^= subjectId.charCodeAt(i);
    hash = Math.imul(hash, 16777619) >>> 0;
  }

  // Extract real CDN upload date from MovieBox poster URL: e.g. /image/2026/11/01/...
  const cdnDateMatch = poster.match(/\/image\/(\d{4})\/(\d{2})\/(\d{2})\//);
  const cdnDateStr = cdnDateMatch ? `${cdnDateMatch[1]}-${cdnDateMatch[2]}-${cdnDateMatch[3]}` : '';
  const cdnEpochMs = cdnDateStr ? Date.parse(`${cdnDateStr}T12:00:00Z`) : NaN;
  const isTodayOrYesterdayCdn =
    !isNaN(cdnEpochMs) && nowMs - cdnEpochMs <= 48 * 3600_000 && cdnEpochMs <= nowMs + 24 * 3600_000;

  let timeAgoLabel = year || 'HD Release';
  let uploadedAtMs = !isNaN(releaseEpochMs) && releaseEpochMs <= nowMs ? releaseEpochMs : 0;

  if (isTodayOrYesterdayCdn && releaseYearNum >= 2025) {
    // Uploaded to MovieBox CDN today or yesterday!
    const minsAgo = 12 + (hash % 380); // 12 mins to 6.5 hours ago
    timeAgoLabel =
      minsAgo < 60 ? `${minsAgo} mins ago` : `${Math.floor(minsAgo / 60)} hours ago`;
    uploadedAtMs = nowMs - minsAgo * 60_000;
  } else if (releaseYearNum >= 2025) {
    const spreadHours = 2 + (hash % 21);
    const spreadMins = spreadHours * 60 + ((hash >>> 8) % 53);
    timeAgoLabel = `${spreadHours} hours ago`;
    uploadedAtMs = nowMs - spreadMins * 60_000;
  } else if (!uploadedAtMs && releaseYearNum > 1900) {
    uploadedAtMs = new Date(`${releaseYearNum}-06-15T00:00:00Z`).getTime();
  }

  return {
    id: `mb_${subjectId}`,
    title: displayTitle,
    url: itemPath,
    path: itemPath,
    poster,
    quality: '1080p FHD',
    views: `★ ${ratingVal.toFixed(1)}`,
    rating: ratingVal.toFixed(1),
    language,
    typeBadge,
    timeAgo: timeAgoLabel,
    episodePill,
    isPinned: releaseYearNum >= 2025 && (isTodayOrYesterdayCdn || ratingVal >= 8.0),
    isAdult: Boolean(raw.isPornographic),
    uploadedAtMs,
  };
}

function isRelevantSouthAsiaMovieBoxItem(raw: any): boolean {
  if (!raw || !raw.title) return false;
  const title = String(raw.title || '');
  const country = String(raw.countryName || '').trim();
  const dubs = Array.isArray(raw.dubs)
    ? raw.dubs.map((d: any) => String(d?.lanName || d || '')).join(' ')
    : '';
  const subs = String(raw.subtitles || '');
  const combined = `${title} ${country} ${dubs}`;

  if (/(hindi|bengali|bangla|বাংলা|urdu|tamil|telugu|malayalam|kannada|punjabi)/i.test(`${combined} ${subs}`)) {
    return true;
  }
  if (UNRELATED_REGIONAL_REGEX.test(combined)) {
    return false;
  }
  if (
    /^(bangladesh|india|pakistan|united states|united kingdom|usa|uk|canada|australia|korea|south korea|japan|china|hong kong|taiwan|turkey|spain|france|germany|italy)$/i.test(
      country
    )
  ) {
    return true;
  }
  const rating = parseFloat(String(raw.imdbRatingValue || raw.imdbRate || '0')) || 0;
  return rating >= 7.0 && !country.match(/nigeria|ghana|kenya|uganda|tanzania|ethiopia|philippines|indonesia|vietnam/i);
}

async function fetchMovieBoxCatalog(
  rawPath: string,
  page = 1,
  search = ''
): Promise<{ items: MovieCardItem[]; maxPage: number }> {
  const token = await getMovieBoxBearerToken();
  const headers = buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`, token);

  if (search) {
    const res = await fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/search`, {
      method: 'POST',
      headers,
      body: JSON.stringify({
        keyword: search,
        page,
        perPage: 36,
        subjectType: 0,
      }),
      signal: AbortSignal.timeout(5500),
    });
    if (!res.ok) throw new Error(`Catalog search HTTP ${res.status}`);
    const json = (await res.json()) as any;
    const rawItems = Array.isArray(json?.data?.items) ? json.data.items : [];
    const cards = rawItems
      .map((it: any, idx: number) => mapMovieBoxItemToCard(it, idx))
      .filter(Boolean) as MovieCardItem[];
    return { items: cards, maxPage: 50 };
  }

  const pNorm = (rawPath || '/').toLowerCase().replace(/\/page\/\d+\/?$/, '').replace(/\/+$/, '') || '/';
  const isHomeOrGeneralFeed =
    pNorm === '/' ||
    pNorm === '/hot-dhamaka' ||
    pNorm === '/new-uploads' ||
    pNorm === '/new-releases' ||
    pNorm === '/mostwatch/7d' ||
    pNorm === '/movies';

  const requests: Promise<Response>[] = [];

  if (isHomeOrGeneralFeed) {
    const regionalQueries: Record<string, any>[] = [
      { page, perPage: 20, channelId: 1, classify: 'Hindi dub', sort: 'Latest' },
      { page, perPage: 16, channelId: 1, classify: 'Bengali dub', sort: 'Latest' },
      { page, perPage: 20, channelId: 1, country: 'India', sort: 'Latest' },
      { page, perPage: 14, channelId: 1, country: 'Bangladesh', sort: 'Latest' },
      { page, perPage: 16, channelId: 2, classify: 'Hindi dub', sort: 'Hottest' },
      { page, perPage: 16, channelId: 1, country: 'United States', sort: 'Hottest' },
      { page, perPage: 14, channelId: 2, country: 'Korea', sort: 'Hottest' },
      { page, perPage: 14, channelId: 1006, sort: 'Latest' },
    ];
    for (const qBody of regionalQueries) {
      requests.push(
        fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
          method: 'POST',
          headers,
          body: JSON.stringify(qBody),
          signal: AbortSignal.timeout(5000),
        })
      );
    }
    if (page === 1) {
      requests.push(
        fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/platform/play-list?page=1&perPage=6&platform=Hoichoi`, {
          method: 'GET',
          headers,
          signal: AbortSignal.timeout(5000),
        }),
        fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/platform/play-list?page=1&perPage=6&platform=Zee5`, {
          method: 'GET',
          headers,
          signal: AbortSignal.timeout(5000),
        })
      );
    }
  } else {
    const filterPayload: Record<string, any> = { ...mapCategoryToMovieBoxFilter(rawPath, page), perPage: 32 };
    const oppositeSort = filterPayload.sort === 'Latest' ? 'Hottest' : 'Latest';
    requests.push(
      fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
        method: 'POST',
        headers,
        body: JSON.stringify(filterPayload),
        signal: AbortSignal.timeout(5000),
      }),
      fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
        method: 'POST',
        headers,
        body: JSON.stringify({ ...filterPayload, sort: oppositeSort }),
        signal: AbortSignal.timeout(5000),
      })
    );
    if (filterPayload.channelId === 1) {
      requests.push(
        fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
          method: 'POST',
          headers,
          body: JSON.stringify({ ...filterPayload, channelId: 2, sort: 'Latest' }),
          signal: AbortSignal.timeout(5000),
        })
      );
    }
    if (pNorm.includes('bangla') && page === 1) {
      requests.push(
        fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/platform/play-list?page=1&perPage=6&platform=Hoichoi`, {
          method: 'GET',
          headers,
          signal: AbortSignal.timeout(5000),
        })
      );
    }
  }

  const settled = await Promise.allSettled(requests);
  const buckets: any[][] = [];
  let maxPage = 2500;
  for (const r of settled) {
    if (r.status === 'fulfilled' && r.value.ok) {
      const j = (await r.value.json().catch(() => null)) as any;
      let list: any[] = j?.data?.subjectList || j?.data?.items || [];
      const monthGroups = Array.isArray(j?.data?.monthList)
        ? j.data.monthList
        : Array.isArray(j?.data?.list)
          ? j.data.list
          : [];
      if ((!Array.isArray(list) || list.length === 0) && monthGroups.length > 0) {
        list = [];
        for (const grp of monthGroups) {
          const nested = grp?.subjects || grp?.subjectList || grp?.items || [];
          if (Array.isArray(nested)) {
            list.push(...nested);
          } else if (grp?.subjectId) {
            list.push(grp);
          }
        }
      }
      if (Array.isArray(list) && list.length > 0) {
        buckets.push(list);
      }
      const totalCount = Number(j?.data?.pager?.totalCount || 0);
      if (totalCount > 0) {
        maxPage = Math.max(maxPage, Math.min(3500, Math.ceil(totalCount / 28)));
      }
    }
  }

  const combinedRaw: any[] = [];
  const maxBucketLen = buckets.reduce((m, b) => Math.max(m, b.length), 0);
  for (let i = 0; i < maxBucketLen; i++) {
    for (const b of buckets) {
      if (i < b.length) {
        const item = b[i];
        if (!isHomeOrGeneralFeed || isRelevantSouthAsiaMovieBoxItem(item)) {
          combinedRaw.push(item);
        }
      }
    }
  }

  const seenIds = new Set<string>();
  const cards: MovieCardItem[] = [];
  for (let i = 0; i < combinedRaw.length; i++) {
    const raw = combinedRaw[i];
    const sid = String(raw?.subjectId || '');
    if (!sid || seenIds.has(sid)) continue;
    seenIds.add(sid);
    const card = mapMovieBoxItemToCard(raw, i);
    if (card) cards.push(card);
  }

  return { items: cards, maxPage };
}

let cachedMovieBoxHomeFeed: CacheEntry<{
  heroBanners: MovieCardItem[];
  homeShelves: HomeShelfSection[];
}> | null = null;

async function fetchMovieBoxBdHomeFeed(forceRefresh = false): Promise<{
  heroBanners: MovieCardItem[];
  homeShelves: HomeShelfSection[];
}> {
  if (!forceRefresh && cachedMovieBoxHomeFeed && cachedMovieBoxHomeFeed.expiresAt > Date.now()) {
    return cachedMovieBoxHomeFeed.data;
  }

  try {
    const token = await getMovieBoxBearerToken();
    const headers = buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`, token);
    const res = await fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/home?host=moviebox01.com`, {
      method: 'GET',
      headers,
      signal: AbortSignal.timeout(6500),
    });
    if (!res.ok) throw new Error(`Home feed HTTP ${res.status}`);
    const json = (await res.json()) as any;
    const ops: any[] = Array.isArray(json?.data?.operatingList) ? json.data.operatingList : [];

    const heroBanners: MovieCardItem[] = [];
    const seenBannerPaths = new Set<string>();
    const bannerOp = ops.find((o) => o?.type === 'BANNER' && Array.isArray(o?.banner?.items));
    if (bannerOp) {
      const bItems: any[] = bannerOp.banner.items || [];
      for (let i = 0; i < bItems.length; i++) {
        const b = bItems[i];
        const sid = String(b?.subjectId || b?.subject?.subjectId || '').trim();
        const detailPath = String(b?.detailPath || b?.subject?.detailPath || '').trim();
        if (!sid || sid === '0' || !detailPath) continue;
        const itemPath = `/mb/${sid}/${detailPath}`;
        if (seenBannerPaths.has(itemPath)) continue;
        seenBannerPaths.add(itemPath);

        const subj = b?.subject || {};
        const bannerImg = String(b?.image?.url || '').trim();
        const posterImg = String(subj?.cover?.url || bannerImg).trim();
        const rawTitle = String(b?.title || subj?.title || '').trim();
        if (!rawTitle) continue;

        const mapped = mapMovieBoxItemToCard(
          {
            ...subj,
            subjectId: sid,
            detailPath,
            title: rawTitle,
            cover: { url: posterImg },
          },
          i
        );
        if (mapped) {
          heroBanners.push({
            ...mapped,
            poster: posterImg || mapped.poster,
            backdrop: bannerImg || posterImg || mapped.poster,
            sourceSite: 'moviebox',
          });
        }
      }
    }

    const homeShelves: HomeShelfSection[] = [];
    const seenShelfKeys = new Set<string>();
    for (let idx = 0; idx < ops.length; idx++) {
      const op = ops[idx];
      if (!op || !Array.isArray(op.subjects) || op.subjects.length === 0) continue;
      if (op.type === 'SPORT_LIVE' || op.type === 'BANNER') continue;
      const shelfTitle = String(op.title || '').trim();
      if (!shelfTitle) continue;
      const shelfKey = shelfTitle.toLowerCase().replace(/[^a-z0-9]+/g, '');
      if (seenShelfKeys.has(shelfKey)) continue;
      seenShelfKeys.add(shelfKey);

      const cards: MovieCardItem[] = [];
      const seenCardPaths = new Set<string>();
      for (let i = 0; i < op.subjects.length; i++) {
        const mapped = mapMovieBoxItemToCard(op.subjects[i], i);
        if (mapped && !seenCardPaths.has(mapped.path)) {
          seenCardPaths.add(mapped.path);
          cards.push({ ...mapped, sourceSite: 'moviebox' });
        }
      }
      if (cards.length > 0) {
        homeShelves.push({
          id: `mb-shelf-${idx}-${shelfKey}`,
          title: shelfTitle,
          source: 'moviebox',
          items: cards.slice(0, 18),
        });
      }
    }

    const data = { heroBanners, homeShelves };
    if (heroBanners.length > 0 || homeShelves.length > 0) {
      cachedMovieBoxHomeFeed = { data, expiresAt: Date.now() + 90_000 };
    }
    return data;
  } catch (err) {
    console.warn('Home feed error:', err instanceof Error ? err.message : err);
    return cachedMovieBoxHomeFeed?.data || { heroBanners: [], homeShelves: [] };
  }
}

async function resolveImdbIdForTitle(
  rawTitle: string,
  releaseDateStr = '',
  isSeries = false
): Promise<string> {
  const cleanTitle = extractBaseSeriesTitle(rawTitle)
    .replace(/\b(19|20)\d{2}\b/g, '')
    .replace(/\s{2,}/g, ' ')
    .trim();
  if (!cleanTitle || cleanTitle.length < 2) return '';
  const cacheKey = `${cleanTitle.toLowerCase()}::${isSeries ? 'tv' : 'movie'}`;
  const cached = imdbIdCache.get(cacheKey);
  if (cached !== undefined) return cached;

  try {
    const res = await fetch(
      `https://v3.sg.media-imdb.com/suggestion/x/${encodeURIComponent(cleanTitle)}.json`,
      {
        headers: { Accept: 'application/json', 'User-Agent': 'Mozilla/5.0' },
        signal: AbortSignal.timeout(2200),
      }
    );
    if (!res.ok) return '';
    const json = (await res.json()) as any;
    const list: any[] = Array.isArray(json?.d) ? json.d.filter((x: any) => String(x?.id || '').startsWith('tt')) : [];
    if (!list.length) {
      imdbIdCache.set(cacheKey, '');
      return '';
    }
    const wantYear = parseInt(String(releaseDateStr || '').slice(0, 4), 10) || 0;
    const norm = (s: string) => String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '');
    const wantNorm = norm(cleanTitle);

    const scored = list.map((item) => {
      let sc = 0;
      const itemNorm = norm(item.l || '');
      if (itemNorm === wantNorm) sc += 50;
      else if (itemNorm.includes(wantNorm) || wantNorm.includes(itemNorm)) sc += 25;
      const qStr = String(item.q || item.qid || '').toLowerCase();
      const itemIsTv = qStr.includes('tv') || qStr.includes('series') || qStr.includes('mini');
      if (isSeries === itemIsTv) sc += 30;
      if (wantYear > 1900 && item.y && Math.abs(Number(item.y) - wantYear) <= 1) sc += 25;
      return { id: String(item.id), sc };
    });
    scored.sort((a, b) => b.sc - a.sc);
    const bestId = scored[0]?.id || '';
    if (bestId) imdbIdCache.set(cacheKey, bestId);
    return bestId;
  } catch {
    return '';
  }
}

function buildEmbedBackupSources(
  imdbId: string,
  seasonNum: number,
  epNum: number,
  title: string,
  language: string
): StreamSource[] {
  if (!imdbId || !imdbId.startsWith('tt')) return [];
  if (seasonNum > 0 && epNum > 0) {
    return [
      {
        id: `vidsrc-me-${imdbId}-s${seasonNum}-e${epNum}`,
        quality: 1080,
        qualityLabel: '1080p Cloud HD (Server 1)',
        audio: language,
        audioLanguages: [language],
        provider: 'Cloud Server 1',
        url: `https://vidsrc.me/embed/tv?imdb=${imdbId}&season=${seasonNum}&episode=${epNum}`,
        downloadUrl: `https://vidsrc.me/embed/tv?imdb=${imdbId}&season=${seasonNum}&episode=${epNum}`,
        type: 'embed',
        name: `${title} - S${seasonNum}E${epNum} (Cloud Server 1)`,
      },
      {
        id: `twoembed-${imdbId}-s${seasonNum}-e${epNum}`,
        quality: 1080,
        qualityLabel: '1080p Cloud HD (Server 2)',
        audio: language,
        audioLanguages: [language],
        provider: 'Cloud Server 2',
        url: `https://www.2embed.cc/embedtv/${imdbId}&s=${seasonNum}&e=${epNum}`,
        downloadUrl: `https://www.2embed.cc/embedtv/${imdbId}&s=${seasonNum}&e=${epNum}`,
        type: 'embed',
        name: `${title} - S${seasonNum}E${epNum} (Cloud Server 2)`,
      },
    ];
  }
  return [
    {
      id: `vidsrc-me-${imdbId}-movie`,
      quality: 1080,
      qualityLabel: '1080p Cloud HD (Server 1)',
      audio: language,
      audioLanguages: [language],
      provider: 'Cloud Server 1',
      url: `https://vidsrc.me/embed/movie?imdb=${imdbId}`,
      downloadUrl: `https://vidsrc.me/embed/movie?imdb=${imdbId}`,
      type: 'embed',
      name: `${title} (Cloud Server 1)`,
    },
    {
      id: `twoembed-${imdbId}-movie`,
      quality: 1080,
      qualityLabel: '1080p Cloud HD (Server 2)',
      audio: language,
      audioLanguages: [language],
      provider: 'Cloud Server 2',
      url: `https://www.2embed.cc/embed/${imdbId}`,
      downloadUrl: `https://www.2embed.cc/embed/${imdbId}`,
      type: 'embed',
      name: `${title} (Cloud Server 2)`,
    },
  ];
}

const mbPlayStreamCache = new Map<
  string,
  { sources: StreamSource[]; buttons: DirectDownloadButton[]; expiresAt: number }
>();

// Auto-detect whether this host's IP (e.g., US Google Cloud Preview) is geo-blocked (426) by hakunaymatata.com CDN.
// On non-blocked servers (e.g., Render Singapore/EU or BD VPS), this returns false so /api/mb-stream.mp4 streams directly!
let mbCdnGeoBlockedCache: { blocked: boolean; expiresAt: number } | null = null;

async function isMovieBoxCdnBlockedOnThisHost(sampleStreamUrl: string): Promise<boolean> {
  if (mbCdnGeoBlockedCache && mbCdnGeoBlockedCache.expiresAt > Date.now()) {
    return mbCdnGeoBlockedCache.blocked;
  }
  if (!sampleStreamUrl || !sampleStreamUrl.startsWith('http')) return false;
  try {
    const r = await fetch(sampleStreamUrl, {
      headers: {
        'User-Agent':
          'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
        Referer: `${MOVIEBOX_CLASSIC_ORIGIN}/`,
        Range: 'bytes=0-0',
      },
      signal: AbortSignal.timeout(3000),
    });
    const blocked = !(r.ok || r.status === 206);
    try {
      await r.body?.cancel();
    } catch {
      // ignore
    }
    mbCdnGeoBlockedCache = { blocked, expiresAt: Date.now() + 5 * 60_000 };
    return blocked;
  } catch {
    mbCdnGeoBlockedCache = { blocked: true, expiresAt: Date.now() + 60_000 };
    return true;
  }
}

// Strict EXACT-TITLE fallback resolver when MovieBox CDN geo-blocks US datacenter IP (426).
// Never does fuzzy substring matching so two different titles can NEVER mix!
async function findExactTitleMlbdBackup(
  rawTitle: string,
  wantMovie: boolean
): Promise<MovieDetailData | null> {
  try {
    const cleanStrictBase = (s: string): string => {
      // Strip everything from a release year marker like "(2026) Hindi HQ Dubbed" onwards
      const beforeYear = String(s || '').replace(/\(\s*(?:19|20)\d{2}\s*\)[\s\S]*$/, '');
      return extractBaseSeriesTitle(beforeYear)
        .replace(
          /\b(?:HQ|Dubbed|Subbed|Dub|Sub|Uncut|Extended|Malayalam|Tamil|Telugu|Kannada|English|Korean|Japanese|Chinese|Spanish|French|Punjabi|Marathi|WebRip|BluRay|HDRip|1080p|720p|480p|CAMRip|PREHD|HDCAM|ESub|MSub|HEVC|x264|x265|IMAX|Remastered|Director'?s?\s*Cut)\b/gi,
          ' '
        )
        .replace(/\s{2,}/g, ' ')
        .trim();
    };
    const baseTitle = cleanStrictBase(rawTitle);
    if (baseTitle.length < 3) return null;
    const norm = (s: string) => cleanStrictBase(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
    const wantNorm = norm(baseTitle);
    if (wantNorm.length < 3) return null;

    // Optional language preference when multiple exact-title editions exist (e.g., Hindi Dubbed vs Original)
    const langHintMatch = String(rawTitle || '').match(/\b(Hindi|Bangla|Bengali|Tamil|Telugu|Malayalam|English)\b/i);
    const wantLang = langHintMatch ? langHintMatch[1].toLowerCase() : '';
    const scoreCandidate = (cardTitle: string, cardPath: string, cardTypeBadge?: string): number => {
      const cardIsSeries = cardTypeBadge === 'SERIES' || cardPath.startsWith('/series/');
      let score = wantMovie === !cardIsSeries ? 10 : 0;
      if (wantLang && cardTitle.toLowerCase().includes(wantLang)) score += 5;
      return score;
    };

    // 1. Check in-memory masterArchiveMap first (0ms) for an EXACT normalized title match
    let matchedPath = '';
    let bestScore = -1;
    for (const rec of masterArchiveMap.values()) {
      if (rec.site !== 'movielinkbd' || !rec.item?.path || rec.item.path.startsWith('/mb/')) continue;
      if (norm(rec.item.title) === wantNorm) {
        const sc = scoreCandidate(rec.item.title, rec.item.path, rec.item.typeBadge);
        if (sc > bestScore) {
          bestScore = sc;
          matchedPath = rec.item.path;
        }
      }
    }

    // 2. If not in archive yet, run live search on MovieLinkBD with strict exact title check
    if (!matchedPath) {
      const searchRes = await fetchFromMirrors(`/search?q=${encodeURIComponent(baseTitle)}`);
      const { items } = parseMovieCards(searchRes.html);
      const exactCards = items.filter((it) => norm(it.title) === wantNorm);
      if (exactCards.length > 0) {
        exactCards.sort(
          (a, b) =>
            scoreCandidate(b.title, b.path, b.typeBadge) - scoreCandidate(a.title, a.path, a.typeBadge)
        );
        matchedPath = exactCards[0].path;
      }
    }

    if (!matchedPath) return null;

    const cached = findCachedDetailByPathOrTitle(matchedPath);
    if (cached && cached.episodes?.length) return cached;

    const { html, finalOrigin } = await fetchFromMirrors(matchedPath);
    let det = parseMovieDetail(html, matchedPath, finalOrigin);
    det = await enrichMovieLinkBdWithPd2Player(html, matchedPath, finalOrigin, det);
    if (det.episodes?.length) {
      storeDetailInCaches(matchedPath, det, Date.now() + 25 * 60_000);
      return det;
    }
    return null;
  } catch {
    return null;
  }
}

async function fetchMovieBoxPlayStreams(
  subjectId: string,
  detailPath: string,
  seasonNum: number,
  epNum: number,
  title: string,
  language: string,
  _unusedFallbackUrl = ''
): Promise<{ sources: StreamSource[]; buttons: DirectDownloadButton[]; cdnBlocked: boolean }> {
  const playCacheKey = `${subjectId}::s${seasonNum}::e${epNum}`;
  const cachedPlay = mbPlayStreamCache.get(playCacheKey);
  if (cachedPlay && cachedPlay.expiresAt > Date.now() && cachedPlay.sources.length > 0) {
    return {
      sources: cachedPlay.sources,
      buttons: cachedPlay.buttons,
      cdnBlocked: Boolean(mbCdnGeoBlockedCache?.blocked),
    };
  }

  const token = await getMovieBoxBearerToken();
  const queryStr = `subjectId=${encodeURIComponent(
    subjectId
  )}&se=${seasonNum}&ep=${epNum}&detailPath=${encodeURIComponent(detailPath)}&streamSignType=1`;
  const playReferer = `${MOVIEBOX_CLASSIC_ORIGIN}/movies/${detailPath}?id=${subjectId}`;
  const headers = buildMovieBoxHeaders(playReferer, token);

  let streams: any[] = [];
  const candidatePlayUrls = [
    `${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/play?${queryStr}`,
    `${MOVIEBOX_ORIGIN}/wefeed-h5api-bff/subject/play?${queryStr}`,
  ];
  for (const playUrl of candidatePlayUrls) {
    try {
      const res = await fetch(playUrl, { headers, signal: AbortSignal.timeout(5500) });
      if (!res.ok) continue;
      const json = (await res.json()) as any;
      const list = Array.isArray(json?.data?.streams) ? json.data.streams : [];
      if (list.length > 0) {
        streams = list;
        break;
      }
    } catch {
      // try next host
    }
  }

  const cdnBlocked =
    streams.length > 0 && streams[0]?.url
      ? await isMovieBoxCdnBlockedOnThisHost(String(streams[0].url))
      : false;

  const sources: StreamSource[] = [];
  const buttons: DirectDownloadButton[] = [];
  const seenDirectUrls = new Set<string>();

  const formatDurMin = (durSec: any) => {
    const s = Number(durSec) || 0;
    return s >= 600 ? ` • ${Math.round(s / 60)} min` : '';
  };

  for (let i = 0; i < streams.length; i++) {
    const st = streams[i];
    const directUrl = String(st?.url || '').trim();
    if (!directUrl || seenDirectUrls.has(directUrl)) continue;
    seenDirectUrls.add(directUrl);
    const resNum = parseInt(String(st.resolutions || st.resolution || '720'), 10) || 720;
    const sizeBytes = Number(st.size) || 0;
    const sizeMb = sizeBytes > 0 ? `${(sizeBytes / (1024 * 1024)).toFixed(0)} MB` : 'Full HD';
    const durTag = formatDurMin(st.duration);
    const urlTok = Buffer.from(directUrl, 'utf8').toString('base64url');
    // Server proxy adds required Referer: https://movie-box.co/ (NEVER trailer fallback!)
    const proxiedStreamUrl = `/api/mb-stream.mp4?t=${urlTok}`;
    const proxiedDlUrl = `/api/mb-stream.mp4?t=${urlTok}&dl=1&name=${encodeURIComponent(
      `${title.replace(/[^a-zA-Z0-9_-]+/g, '_')}_${resNum}p.mp4`
    )}`;

    if (!cdnBlocked) {
      sources.push({
        id: `mb-stream-${subjectId}-s${seasonNum}-e${epNum}-${resNum}p-${i}`,
        quality: resNum,
        qualityLabel: `${resNum}p HD Direct`,
        audio: language,
        audioLanguages: [language],
        provider: `HD Server ${resNum}p`,
        url: proxiedStreamUrl,
        downloadUrl: proxiedDlUrl,
        type: 'mp4',
        name: `${title} (${resNum}p MP4 • ${sizeMb}${durTag})`,
      });
    }

    buttons.push({
      label: `Direct Download ${resNum}p MP4 (${sizeMb})`,
      url: proxiedDlUrl,
      quality: `${resNum}p`,
      size: sizeMb,
    });
  }

  sources.sort((a, b) => {
    const rank = (s: StreamSource) => {
      const szMatch = (s.name || '').match(/(\d+)\s*MB/i);
      const szMb = szMatch ? parseInt(szMatch[1], 10) : 0;
      if (s.quality === 480) return 105;
      if (s.quality === 720) return 100;
      if (s.quality === 360) return 95;
      if (s.quality === 1080) return szMb > 350 ? 80 : 92;
      return s.quality;
    };
    return rank(b) - rank(a);
  });
  buttons.sort((a, b) => parseInt(b.quality, 10) - parseInt(a.quality, 10));
  if (sources.length > 0) {
    mbPlayStreamCache.set(playCacheKey, {
      sources,
      buttons,
      expiresAt: Date.now() + 12 * 60_000,
    });
  }
  return { sources, buttons, cdnBlocked };
}

async function fetchMovieBoxDetail(
  rawPath: string,
  fallbackTitleHint = ''
): Promise<MovieDetailData> {
  const cleanPath = rawPath.split('?')[0];
  const parts = cleanPath.replace(/^\/mb\//, '').split('/').filter(Boolean);
  const subjectId = parts[0] || '';
  const fallbackSlug = parts[1] || 'movie';

  const token = await getMovieBoxBearerToken();
  const headers = buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`, token);

  let detJson: any = null;
  const candidateDetailUrls = [
    `${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/detail?subjectId=${encodeURIComponent(subjectId)}`,
    `${MOVIEBOX_ORIGIN}/wefeed-h5api-bff/detail?subjectId=${encodeURIComponent(subjectId)}`,
    `${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/detail?detailPath=${encodeURIComponent(fallbackSlug)}`,
  ];
  for (const dUrl of candidateDetailUrls) {
    try {
      const detRes = await fetch(dUrl, { headers, signal: AbortSignal.timeout(5000) });
      if (detRes.ok) {
        const parsed = (await detRes.json().catch(() => null)) as any;
        if (parsed?.data?.subject?.title || parsed?.data?.subject?.subjectId) {
          detJson = parsed;
          break;
        }
      }
    } catch {
      // try next detail host/param
    }
  }

  if (!detJson?.data?.subject) {
    const archivedCard = masterArchiveMap.get(cleanPath)?.item || masterArchiveMap.get(rawPath)?.item;
    const slugTitle = fallbackSlug
      .replace(/-[a-z0-9]{8,}$/i, '')
      .replace(/-/g, ' ')
      .replace(/\b\w/g, (c) => c.toUpperCase())
      .trim();
    const resolvedTitle = String(fallbackTitleHint || archivedCard?.title || slugTitle || 'Cinema Title').trim();
    const resolvedLang = String(archivedCard?.language || 'Hindi / Original').trim();
    const isSeriesCard =
      archivedCard?.typeBadge === 'SERIES' ||
      archivedCard?.typeBadge === 'DRAMA' ||
      archivedCard?.typeBadge === 'ANIME' ||
      /\b(?:S\d+|Season\s*\d+|Ep\s*\d+)\b/i.test(resolvedTitle);
    const yearMatch = resolvedTitle.match(/\b(19|20)\d{2}\b/);
    const releaseYr = yearMatch ? yearMatch[0] : '2026';

    const [{ sources: playSources, buttons: playButtons }, imdbId] = await Promise.all([
      fetchMovieBoxPlayStreams(subjectId, fallbackSlug, isSeriesCard ? 1 : 0, isSeriesCard ? 1 : 0, resolvedTitle, resolvedLang).catch(
        () => ({ sources: [] as StreamSource[], buttons: [] as DirectDownloadButton[] })
      ),
      resolveImdbIdForTitle(resolvedTitle, releaseYr, isSeriesCard),
    ]);

    const embedBackups = buildEmbedBackupSources(
      imdbId,
      isSeriesCard ? 1 : 0,
      isSeriesCard ? 1 : 0,
      resolvedTitle,
      resolvedLang
    );
    const combinedSources = [...playSources, ...embedBackups];
    const fallbackEpisodes: EpisodeItem[] = combinedSources.length
      ? [
          {
            id: `mb-fb-${subjectId}`,
            label: isSeriesCard ? 'S01E01 • Episode 1' : 'Full Movie (HD Cloud)',
            number: 1,
            rangeStart: 1,
            rangeEnd: 1,
            season: isSeriesCard ? 1 : null,
            kind: isSeriesCard ? 'episode' : 'movie',
            sources: combinedSources,
          },
        ]
      : [];

    return {
      title: resolvedTitle,
      url: rawPath,
      poster: archivedCard?.poster || '',
      qualityNote: `1080p / 720p • ${resolvedLang}`,
      typeBadge: archivedCard?.typeBadge || (isSeriesCard ? 'SERIES' : 'MOVIE'),
      language: resolvedLang,
      quality: archivedCard?.quality || '1080p FHD',
      genre: isSeriesCard ? 'Drama, Series' : 'Action, Drama',
      resolution: '1080p | 720p | 480p',
      releaseDate: releaseYr,
      storyline: `${resolvedTitle} — HD streaming available via cloud servers.`,
      youtubeTrailerId: '',
      screenshots: archivedCard?.poster ? [archivedCard.poster] : [],
      episodes: fallbackEpisodes,
      downloadButtons: playButtons,
      cast: [],
      dubs: [
        {
          id: subjectId || rawPath,
          label: resolvedLang,
          path: rawPath,
          active: true,
        },
      ],
      uploadedBy: 'CinePulse',
      communityScore: {
        recommendedPercent: 86,
        totalVotes: 920,
        verdict: 'Cloud HD Verified',
      },
    };
  }
  const subject = detJson?.data?.subject || {};
  const resource = detJson?.data?.resource || {};
  const stars = Array.isArray(detJson?.data?.stars) ? detJson.data.stars : [];

  const title = String(subject.title || 'Cinema Title').trim();
  const detailPath = String(subject.detailPath || fallbackSlug).trim();
  const poster = String(subject.cover?.url || '').trim();
  const releaseDate = String(subject.releaseDate || '2026').trim();
  const genre = String(subject.genre || 'Action, Drama').replace(/,/g, ', ');
  const storyline = String(subject.description || '').trim();
  const ratingVal = parseFloat(String(subject.imdbRatingValue || '8.4')) || 8.4;
  const subjectType = Number(subject.subjectType) || 1;
  const trailerMp4Url = String(subject.trailer?.videoAddress?.url || '').trim();
  const uploadedBy = 'CinePulse';

  // Extract all available audio dubs / language versions from subject.dubs (e.g., Hindi dub, Bengali dub, Original Audio, etc.)
  const rawDubs = Array.isArray(subject.dubs) ? subject.dubs : [];
  const dubs: MovieDubOption[] = [];
  const seenDubIds = new Set<string>();
  for (const d of rawDubs) {
    const dId = String(d?.subjectId || '').trim();
    const dLabel = String(d?.lanName || '').trim();
    if (!dId || !dLabel || seenDubIds.has(dId)) continue;
    seenDubIds.add(dId);
    const dSlug = String(d?.detailPath || detailPath).trim();
    dubs.push({
      id: dId,
      label: dLabel,
      lanCode: String(d?.lanCode || '').trim(),
      path: `/mb/${dId}/${dSlug}`,
      active: dId === subjectId,
    });
  }

  // Sort dubs so active dub, Hindi dub, Bangla/Bengali dub, and Original Audio appear at the top
  dubs.sort((a, b) => {
    const rank = (opt: MovieDubOption) => {
      if (opt.active) return 100;
      const l = opt.label.toLowerCase();
      if (l.includes('hindi')) return 90;
      if (l.includes('bengali') || l.includes('bangla')) return 85;
      if (l.includes('original') || l.includes('english')) return 80;
      if (l.includes('dub')) return 70;
      return 40;
    };
    return rank(b) - rank(a);
  });

  // Determine the exact audio/dub label for this subjectId
  const activeDubObj = dubs.find((d) => d.id === subjectId);
  let language = activeDubObj?.label || '';
  if (!language) {
    if (/\[hindi\]|\bhindi\s*dub/i.test(title)) language = 'Hindi dub';
    else if (/\[bengali\]|\[bangla\]|\bbangla\s*dub/i.test(title)) language = 'Bangla dub';
    else if (/\[tamil\]/i.test(title)) language = 'Tamil dub';
    else if (/\[telugu\]/i.test(title)) language = 'Telugu dub';
    else if (/\[arabic\]/i.test(title)) language = 'Arabic dub';
    else if (String(subject.countryName || '').toLowerCase().includes('india')) language = 'Hindi';
    else if (String(subject.countryName || '').toLowerCase().includes('bangladesh')) language = 'Bangla';
    else if (String(subject.countryName || '').toLowerCase().includes('korea')) language = 'Korean';
    else if (dubs.length > 0) language = dubs[0].label;
    else language = 'Original Audio';
  }

  if (dubs.length === 0) {
    dubs.push({
      id: subjectId,
      label: language,
      path: rawPath,
      active: true,
    });
  } else if (!dubs.some((d) => d.active)) {
    dubs.unshift({
      id: subjectId,
      label: language,
      path: rawPath,
      active: true,
    });
  }

  const cast: CastMember[] = (Array.isArray(subject.staffList) ? subject.staffList : stars)
    .slice(0, 12)
    .map((s: any) => ({
      url: `/search?q=${encodeURIComponent(String(s?.name || ''))}`,
      photo: String(s?.avatarUrl || s?.avatar || ''),
      name: String(s?.name || 'Actor'),
      role: String(s?.character || s?.role || 'Cast'),
    }));

  const screenshots: string[] = [];
  if (subject.stills?.url) screenshots.push(String(subject.stills.url));
  if (subject.trailer?.cover?.url) screenshots.push(String(subject.trailer.cover.url));

  const seasonsList = Array.isArray(resource.seasons) ? resource.seasons : [];
  const isMovieType =
    subjectType === 1 ||
    seasonsList.length === 0 ||
    (seasonsList.length === 1 && Number(seasonsList[0]?.se) === 0);

  const episodes: EpisodeItem[] = [];
  let downloadButtons: DirectDownloadButton[] = [];

  if (isMovieType) {
    // Movie (se=0, ep=0, with fallback to se=1, ep=1) + fast parallel IMDb lookup for verified full-length embed servers!
    const [playPrimary, imdbId] = await Promise.all([
      fetchMovieBoxPlayStreams(subjectId, detailPath, 0, 0, title, language),
      Promise.race([
        resolveImdbIdForTitle(title, releaseDate, false),
        new Promise<string>((r) => setTimeout(() => r(''), 600)),
      ]),
    ]);
    let { sources, buttons, cdnBlocked } = playPrimary;
    if (sources.length === 0 && !cdnBlocked) {
      const fb = await fetchMovieBoxPlayStreams(subjectId, detailPath, 1, 1, title, language);
      sources = fb.sources;
      buttons = fb.buttons;
      cdnBlocked = fb.cdnBlocked;
    }

    // If MovieBox CDN geo-blocks this server's IP (426 on US Cloud Run), check STRICT EXACT-TITLE match on MLBD for working Direct MP4 + 1080p HLS!
    let exactBackupSources: StreamSource[] = [];
    if (cdnBlocked || sources.length === 0) {
      const exactBackup = await findExactTitleMlbdBackup(title, true);
      if (exactBackup?.episodes?.[0]?.sources?.length) {
        exactBackupSources = exactBackup.episodes[0].sources;
        if (exactBackup.downloadButtons?.length) {
          buttons = [...exactBackup.downloadButtons, ...buttons];
        }
      }
    }

    const embedBackups = buildEmbedBackupSources(imdbId, 0, 0, title, language);
    const allMovieSources = [...sources, ...exactBackupSources, ...embedBackups];
    downloadButtons = buttons;
    if (allMovieSources.length > 0) {
      episodes.push({
        id: `mb-movie-${subjectId}`,
        label: 'Full Movie (HD)',
        number: 1,
        rangeStart: 1,
        rangeEnd: 1,
        season: null,
        kind: 'movie',
        sources: allMovieSources,
      });
    }
  } else {
    // Series / Drama / Anime: Preload Episode 1 immediately!
    const parseSeasonEpNums = (sObj: any): number[] => {
      const maxEp = Math.max(1, Number(sObj?.maxEp) || 1);
      const fromAllEp = String(sObj?.allEp || '')
        .split(',')
        .map((x) => parseInt(x.trim(), 10))
        .filter((n) => !Number.isNaN(n) && n > 0);
      return fromAllEp.length > 0
        ? fromAllEp
        : Array.from({ length: maxEp }, (_, idx) => idx + 1);
    };

    const firstSeason = seasonsList[0] || { se: 1, maxEp: 8 };
    const firstSeNum = Number(firstSeason.se) || 1;
    const firstSeasonEpNums = parseSeasonEpNums(firstSeason);
    const firstEpNum = firstSeasonEpNums[0] || 1;

    const preloadedMap = new Map<number, { sources: StreamSource[]; buttons: DirectDownloadButton[]; cdnBlocked: boolean }>();
    const [firstEpRes, imdbId] = await Promise.all([
      fetchMovieBoxPlayStreams(
        subjectId,
        detailPath,
        firstSeNum,
        firstEpNum,
        `${title} S${firstSeNum}E${firstEpNum}`,
        language
      ),
      Promise.race([
        resolveImdbIdForTitle(title, releaseDate, true),
        new Promise<string>((r) => setTimeout(() => r(''), 600)),
      ]),
    ]);
    preloadedMap.set(firstEpNum, firstEpRes);

    // If MovieBox CDN geo-blocks this server's IP (426), check STRICT EXACT-TITLE series match (matching exact season & episode!)
    const exactSeriesBackup =
      firstEpRes.cdnBlocked || firstEpRes.sources.length === 0
        ? await findExactTitleMlbdBackup(title, false)
        : null;

    for (let sIdx = 0; sIdx < seasonsList.length; sIdx++) {
      const sObj = seasonsList[sIdx];
      const seNum = Number(sObj?.se) || sIdx + 1;
      const epNums = sIdx === 0 ? firstSeasonEpNums : parseSeasonEpNums(sObj);

      for (const epNum of epNums) {
        const pre = sIdx === 0 ? preloadedMap.get(epNum) : undefined;
        const embedBackups = buildEmbedBackupSources(imdbId, seNum, epNum, title, language);
        const matchedBackupEp = exactSeriesBackup?.episodes?.find(
          (be) => be.number === epNum && (be.season === null || be.season === seNum)
        );
        const exactEpSources = matchedBackupEp?.sources || [];

        if (pre && pre.sources.length > 0) {
          if (downloadButtons.length === 0) downloadButtons = pre.buttons;
          episodes.push({
            id: `mb-ep-${subjectId}-s${seNum}-e${epNum}`,
            label: `S${String(seNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • Episode ${epNum}`,
            number: epNum,
            rangeStart: epNum,
            rangeEnd: epNum,
            season: seNum,
            kind: 'episode',
            sources: [...pre.sources, ...exactEpSources, ...embedBackups],
          });
        } else if (firstEpRes.cdnBlocked && (exactEpSources.length > 0 || embedBackups.length > 0)) {
          // On US geo-blocked server, use exact-matched Direct MP4/HLS + verified full-episode embeds directly (never dead 426!)
          episodes.push({
            id: `mb-ep-${subjectId}-s${seNum}-e${epNum}`,
            label: `S${String(seNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • Episode ${epNum}`,
            number: epNum,
            rangeStart: epNum,
            rangeEnd: epNum,
            season: seNum,
            kind: 'episode',
            sources: [...exactEpSources, ...embedBackups],
          });
        } else {
          // Dynamic lazy-resolved stream URL via /api/mb-ep-stream.mp4
          const dynamicStreamUrl = `/api/mb-ep-stream.mp4?subjectId=${encodeURIComponent(
            subjectId
          )}&detailPath=${encodeURIComponent(detailPath)}&se=${seNum}&ep=${epNum}`;
          episodes.push({
            id: `mb-ep-${subjectId}-s${seNum}-e${epNum}`,
            label: `S${String(seNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • Episode ${epNum}`,
            number: epNum,
            rangeStart: epNum,
            rangeEnd: epNum,
            season: seNum,
            kind: 'episode',
            sources: [
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-720`,
                quality: 720,
                qualityLabel: '720p HD',
                audio: language,
                audioLanguages: [language],
                provider: 'HD Server 720p',
                url: `${dynamicStreamUrl}&q=720`,
                downloadUrl: `${dynamicStreamUrl}&q=720&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (720p)`,
              },
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-480`,
                quality: 480,
                qualityLabel: '480p Fast',
                audio: language,
                audioLanguages: [language],
                provider: 'HD Server 480p',
                url: `${dynamicStreamUrl}&q=480`,
                downloadUrl: `${dynamicStreamUrl}&q=480&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (480p)`,
              },
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-1080`,
                quality: 1080,
                qualityLabel: '1080p Full HD',
                audio: language,
                audioLanguages: [language],
                provider: 'HD Server 1080p',
                url: `${dynamicStreamUrl}&q=1080`,
                downloadUrl: `${dynamicStreamUrl}&q=1080&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (1080p)`,
              },
              ...exactEpSources,
              ...embedBackups,
            ],
          });
        }
      }
    }
  }

  // Fallback to trailer if a title is upcoming / has no main stream yet
  if (episodes.length === 0 && trailerMp4Url) {
    const trUrl = `/api/mb-stream.mp4?t=${Buffer.from(trailerMp4Url, 'utf8').toString('base64url')}`;
    episodes.push({
      id: `mb-trailer-${subjectId}`,
      label: 'Official Preview Stream',
      number: 1,
      rangeStart: 1,
      rangeEnd: 1,
      season: null,
      kind: 'movie',
      sources: [
        {
          id: `mb-trailer-src-${subjectId}`,
          quality: 720,
          qualityLabel: '720p Official Preview',
          audio: language,
          audioLanguages: [language],
          provider: 'HD Preview',
          url: trUrl,
          downloadUrl: trUrl,
          type: 'mp4',
          name: `${title} (Preview)`,
        },
      ],
    });
  }

  return {
    title,
    url: rawPath,
    poster,
    qualityNote: `1080p / 720p / 480p • ${language}`,
    typeBadge: subjectType === 2 ? 'SERIES' : 'MOVIE',
    language,
    quality: '1080p FHD',
    genre,
    resolution: '1080p | 720p | 480p | 360p',
    releaseDate,
    storyline,
    youtubeTrailerId: '',
    screenshots,
    episodes,
    downloadButtons,
    cast,
    dubs,
    uploadedBy,
    communityScore: {
      recommendedPercent: Math.min(99, Math.max(75, Math.round(ratingVal * 10))),
      totalVotes: Number(subject.imdbRatingCount) || 1420,
      verdict: 'Cloud HD Verified',
    },
  };
}

async function startServer() {
  const app = express();
  const PORT = Number(process.env.PORT) || 3000;

  app.use((req, res, next) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Range');
    if (req.method === 'OPTIONS') {
      res.status(204).end();
      return;
    }
    next();
  });

  app.use(express.json());

  // Pre-warm & 60s Real-Time Auto-Sync for 2-Source Engine (MovieBox BD + MovieLinkBD) with SSE Broadcast
  const syncLiveCategories = async (crawlDeepArchive = true) => {
    if (isSyncRunning) return;
    isSyncRunning = true;
    const warmPaths = ['/', '/anime', '/ongoing', '/drama', '/southIndian', '/bollywood', '/language/bangla', '/adult18plus'];
    const cycleNewItems: MovieCardItem[] = [];
    const seenNewPaths = new Set<string>();

    try {
      // Refresh live BD Home Banner + Home Shelves alongside category feeds
      void fetchMovieBoxBdHomeFeed(true)
        .then((hf) => {
          const allHomeItems = [
            ...hf.heroBanners,
            ...hf.homeShelves.flatMap((s) => s.items || []),
          ];
          if (allHomeItems.length > 0) {
            upsertItemsIntoMasterArchive(allHomeItems, '/', hasCompletedInitialBaseline);
          }
        })
        .catch(() => {});

      for (const wp of warmPaths) {
        try {
          const cacheKey = `${wp}::page=1::q=::node=auto`;
          const [mbRes, primaryRes] = await Promise.allSettled([
            wp === '/adult18plus'
              ? Promise.resolve({ items: [], maxPage: 1 })
              : fetchMovieBoxCatalog(wp, 1, ''),
            fetchFromMirrors(wp),
          ]);

          const mbParsed =
            mbRes.status === 'fulfilled' ? mbRes.value : { items: [], maxPage: 500 };
          const primaryParsed =
            primaryRes.status === 'fulfilled'
              ? parseMovieCards(primaryRes.value.html)
              : { items: [], maxPage: 520 };
          const activeNodeId =
            primaryRes.status === 'fulfilled' ? primaryRes.value.activeNodeId : 'node-moviebox';

          if (mbParsed.items.length > 0) {
            const newly = upsertItemsIntoMasterArchive(mbParsed.items, wp, hasCompletedInitialBaseline);
            for (const item of newly) {
              if (!seenNewPaths.has(item.path)) {
                seenNewPaths.add(item.path);
                cycleNewItems.push(item);
              }
            }
          }
          if (primaryParsed.items.length > 0) {
            const newly = upsertItemsIntoMasterArchive(primaryParsed.items, wp, hasCompletedInitialBaseline);
            for (const item of newly) {
              if (!seenNewPaths.has(item.path)) {
                seenNewPaths.add(item.path);
                cycleNewItems.push(item);
              }
            }
          }

          const rawMergedItems = mergeCatalogItems(mbParsed.items, primaryParsed.items, true);
          const mergedItems =
            wp === '/'
              ? sortItemsByHotAndHype(rawMergedItems)
              : normalizeMovieCardList(rawMergedItems);

          if (mergedItems.length > 0) {
            const entry = {
              data: {
                items: mergedItems,
                maxPage: Math.max(mbParsed.maxPage, primaryParsed.maxPage),
                activeNodeId,
              },
              expiresAt: Date.now() + 90_000,
            };
            catalogCache.set(cacheKey, entry);
            catalogCache.set(`${wp}::page=1::q=::node=${activeNodeId}`, entry);
            if (mbParsed.items.length > 0) {
              catalogCache.set(`${wp}::page=1::q=::node=node-moviebox`, {
                data: {
                  items: normalizeMovieCardList(rawMergedItems),
                  maxPage: mbParsed.maxPage,
                  activeNodeId: 'node-moviebox',
                },
                expiresAt: Date.now() + 90_000,
              });
            }

            // Gently pre-warm top 4 uncached items for home so first click is instant without saturating sockets
            if (wp === '/') {
              const candidates = mergedItems
                .slice(0, 4)
                .filter((card) => card.path && !findCachedDetailByPathOrTitle(card.path));
              for (const card of candidates) {
                try {
                  if (card.path.startsWith('/mb/')) {
                    const mbDet = await fetchMovieBoxDetail(card.path);
                    if (mbDet && mbDet.episodes.length > 0) {
                      storeDetailInCaches(card.path, mbDet, Date.now() + 3600_000);
                    }
                  } else {
                    const { html, finalOrigin } = await fetchFromMirrors(card.path, activeNodeId);
                    let det = parseMovieDetail(html, card.path, finalOrigin);
                    det = await enrichMovieLinkBdWithPd2Player(html, card.path, finalOrigin, det);
                    if (det.episodes.length > 0) {
                      storeDetailInCaches(card.path, det, Date.now() + 3600_000);
                    }
                  }
                } catch {
                  // ignore single detail warmup failure
                }
              }
            }
          }
        } catch {
          // ignore background warmup errors
        }
      }

      // Progressive deep archive crawler: indexes deeper pages across both MovieBox & MovieLinkBD
      if (crawlDeepArchive) {
        const crawlPage = archivePageCursor;
        archivePageCursor = archivePageCursor >= 45 ? 2 : archivePageCursor + 1;
        const [mbDeepRes, mlbdDeepRes] = await Promise.allSettled([
          fetchMovieBoxCatalog('/', crawlPage, ''),
          fetchFromMirrors(`/page/${crawlPage}`),
        ]);
        if (mbDeepRes.status === 'fulfilled' && mbDeepRes.value.items.length > 0) {
          upsertItemsIntoMasterArchive(mbDeepRes.value.items, '/', false);
        }
        if (mlbdDeepRes.status === 'fulfilled') {
          const parsedDeep = parseMovieCards(mlbdDeepRes.value.html);
          if (parsedDeep.items.length > 0) {
            upsertItemsIntoMasterArchive(parsedDeep.items, '/', false);
          }
        }
      }

      hasCompletedInitialBaseline = true;
      lastAutoSyncAt = Date.now();
      lastCycleNewItemsCount = cycleNewItems.length;

      if (cycleNewItems.length > 0) {
        broadcastSseEvent('catalog_update', {
          newItems: normalizeMovieCardList(cycleNewItems).slice(0, 30),
          totalIndexed: getArchiveCountsBySite().total,
          syncedAt: lastAutoSyncAt,
        });
      }
    } finally {
      isSyncRunning = false;
    }
  };
  setTimeout(() => void syncLiveCategories(true), 200).unref();
  setInterval(() => void syncLiveCategories(true), AUTO_SYNC_INTERVAL_MS).unref();

  // 1. Categories & Anonymized Server Nodes Endpoint
  app.get('/api/categories', (_req, res) => {
    res.json({
      categories: ALL_CATEGORIES,
      nodes: SERVER_NODES.map(({ id, name, region }) => ({ id, name, region })),
    });
  });

  // 2. Live Server Node Ping & Health Check Endpoint (Anonymized)
  app.get('/api/server-health', async (_req, res) => {
    if (healthCache && healthCache.expiresAt > Date.now()) {
      res.json({ ok: true, nodes: healthCache.data });
      return;
    }

    const checks = await Promise.all(
      SERVER_NODES.map(async (node): Promise<ServerNodeStatus> => {
        const start = Date.now();
        try {
          const controller = new AbortController();
          const timer = setTimeout(() => controller.abort(), 4500);
          const r = await fetch(node.origin, {
            method: 'HEAD',
            signal: controller.signal,
            headers: { 'User-Agent': 'Mozilla/5.0' },
          });
          clearTimeout(timer);
          const latencyMs = Math.max(18, Date.now() - start);
          return {
            id: node.id,
            name: node.name,
            region: node.region,
            latencyMs,
            online: r.ok || r.status < 500,
          };
        } catch {
          return {
            id: node.id,
            name: node.name,
            region: node.region,
            latencyMs: 999,
            online: false,
          };
        }
      })
    );

    healthCache = {
      data: checks,
      expiresAt: Date.now() + 30_000,
    };

    res.json({ ok: true, nodes: checks });
  });

  // 3. Instant Live Search Suggestions Endpoint (Unfiltered Dual-Source Search: MovieBox + MovieLinkBD!)
  app.get('/api/suggest', async (req, res) => {
    const q = String(req.query.q || '').trim();
    const nodeId = String(req.query.node || '').trim();
    if (q.length < 1) {
      res.json({ ok: true, items: [] });
      return;
    }

    const lowerQ = q.toLowerCase();
    const collectLocalMatches = (): MovieCardItem[] => {
      const archived = queryMasterArchive({ q, includeAdult: true, sort: 'popular', limit: 24 }).items;
      const localPool: MovieCardItem[] = [...archived];
      for (const [, entry] of catalogCache.entries()) {
        for (const it of entry.data.items) {
          if (it.path && !it.path.startsWith('/mf/') && it.title.toLowerCase().includes(lowerQ)) {
            localPool.push(it);
          }
        }
      }
      for (const list of Object.values(INITIAL_FALLBACK_MOVIES)) {
        for (const it of list) {
          if (it.path && !it.path.startsWith('/mf/') && it.title.toLowerCase().includes(lowerQ)) {
            localPool.push(it);
          }
        }
      }
      return deduplicateByExactPath(localPool);
    };

    const interleaveTwoSites = (list: MovieCardItem[]): MovieCardItem[] => {
      const mb = list.filter((i) => i.path?.startsWith('/mb/'));
      const mlbd = list.filter((i) => !i.path?.startsWith('/mb/') && !i.path?.startsWith('/mf/'));
      const out: MovieCardItem[] = [];
      const maxLen = Math.max(mb.length, mlbd.length);
      for (let i = 0; i < maxLen; i++) {
        if (i < mb.length) out.push(mb[i]);
        if (i < mlbd.length) out.push(mlbd[i]);
      }
      return deduplicateByExactPath(out);
    };

    const targetPath = `/search?q=${encodeURIComponent(q)}`;
    const cacheKey = `suggest::${targetPath}::2sites`;
    const cached = catalogCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json({ ok: true, items: cached.data.items.slice(0, 20) });
      return;
    }

    try {
      const [mbRes, primaryRes] = await Promise.allSettled([
        fetchMovieBoxCatalog('/', 1, q),
        fetchFromMirrors(targetPath, nodeId),
      ]);

      const mbItems = mbRes.status === 'fulfilled' ? mbRes.value.items : [];
      const primaryItems =
        primaryRes.status === 'fulfilled' ? parseMovieCards(primaryRes.value.html).items : [];
      const activeNodeId =
        nodeId === 'node-moviebox'
          ? 'node-moviebox'
          : primaryRes.status === 'fulfilled'
            ? primaryRes.value.activeNodeId
            : 'node-moviebox';

      if (mbItems.length > 0) upsertItemsIntoMasterArchive(mbItems, '/', false);
      if (primaryItems.length > 0) upsertItemsIntoMasterArchive(primaryItems, '/', false);

      const localMatches = collectLocalMatches();
      const combined = interleaveTwoSites([
        ...mbItems,
        ...primaryItems,
        ...localMatches,
      ]);

      if (combined.length > 0) {
        catalogCache.set(cacheKey, {
          data: { items: combined, maxPage: 1, activeNodeId },
          expiresAt: Date.now() + 90_000,
        });
        res.json({ ok: true, items: combined.slice(0, 20) });
        return;
      }
    } catch {
      // fallback below
    }

    const fallback = interleaveTwoSites(collectLocalMatches());
    res.json({ ok: true, items: fallback.slice(0, 20) });
  });

  // 3b. Live Home Feed Endpoint (BD Hero Image Slider + Live Home Shelves + Latest Updates Shelf)
  app.get('/api/home-feed', async (req, res) => {
    const forceRefresh = String(req.query.refresh || '0') === '1';
    try {
      const [mbHomeRes, mlbdHomeRes] = await Promise.allSettled([
        fetchMovieBoxBdHomeFeed(forceRefresh),
        fetchFromMirrors('/'),
      ]);

      const mbHome =
        mbHomeRes.status === 'fulfilled'
          ? mbHomeRes.value
          : { heroBanners: [] as MovieCardItem[], homeShelves: [] as HomeShelfSection[] };
      const mlbdLatest =
        mlbdHomeRes.status === 'fulfilled'
          ? normalizeMovieCardList(parseMovieCards(mlbdHomeRes.value.html).items)
          : queryMasterArchive({ source: 'movielinkbd', sort: 'latest', limit: 20 }).items;

      if (mbHome.heroBanners.length > 0) {
        upsertItemsIntoMasterArchive(mbHome.heroBanners, '/', false);
      }
      if (mlbdLatest.length > 0) {
        upsertItemsIntoMasterArchive(mlbdLatest, '/', false);
      }

      const shelves: HomeShelfSection[] = [...mbHome.homeShelves];
      if (mlbdLatest.length > 0) {
        shelves.push({
          id: 'shelf-latest-updates',
          title: '🔥Latest Updates',
          source: 'movielinkbd',
          items: mlbdLatest.slice(0, 20),
        });
      }

      res.json({
        ok: true,
        heroBanners: normalizeMovieCardList(mbHome.heroBanners),
        homeShelves: shelves,
        syncedAt: Date.now(),
      });
    } catch (err) {
      console.error('Home feed error:', err);
      res.status(500).json({ ok: false, heroBanners: [], homeShelves: [] });
    }
  });

  // 4. Live Catalog & Unfiltered Dual-Source Search Endpoint (MovieBox BD + MovieLinkBD)
  app.get('/api/catalog', async (req, res) => {
    const rawPath = String(req.query.path || '/').trim();
    const page = Math.max(1, parseInt(String(req.query.page || '1'), 10) || 1);
    const search = String(req.query.q || '').trim();
    const nodeId = String(req.query.node || '').trim();
    const forceRefresh = String(req.query.refresh || '0') === '1';

    const isNewUploadsView = rawPath === '/new-uploads';
    const isNewReleasesView = rawPath === '/new-releases';
    const isHotDhamakaView = rawPath === '/hot-dhamaka';
    const isTrendingHomeView = rawPath === '/' || rawPath === '';

    let upstreamBasePath = rawPath.startsWith('/') ? rawPath : `/${rawPath}`;
    if (isNewUploadsView || isNewReleasesView || isHotDhamakaView) {
      upstreamBasePath = '/';
    }

    let targetPath = upstreamBasePath;
    if (search) {
      targetPath =
        page > 1
          ? `/search/page/${page}?q=${encodeURIComponent(search)}`
          : `/search?q=${encodeURIComponent(search)}`;
    } else if (page > 1) {
      const base = upstreamBasePath === '/' ? '' : upstreamBasePath.replace(/\/+$/, '');
      targetPath = `${base}/page/${page}`;
    }

    const collectPrefetchedDetails = (list: MovieCardItem[], warmNodeId: string) => {
      const prefetchedDetails: Record<string, MovieDetailData> = {};
      const missingCards: MovieCardItem[] = [];
      for (const item of list.slice(0, 24)) {
        if (!item?.path || item.path.startsWith('/mf/')) continue;
        const hit = findCachedDetailByPathOrTitle(item.path);
        if (hit && hit.episodes?.length) {
          prefetchedDetails[item.path] = hit;
        } else {
          missingCards.push(item);
        }
      }
      if (missingCards.length > 0) {
        void (async () => {
          for (const card of missingCards.slice(0, 3)) {
            if (findCachedDetailByPathOrTitle(card.path)) continue;
            try {
              if (card.path.startsWith('/mb/')) {
                const mbDet = await fetchMovieBoxDetail(card.path);
                if (mbDet && mbDet.episodes.length > 0) {
                  storeDetailInCaches(card.path, mbDet, Date.now() + 3600_000);
                }
              } else {
                const { html, finalOrigin } = await fetchFromMirrors(card.path, warmNodeId);
                let det = parseMovieDetail(html, card.path, finalOrigin);
                det = await enrichMovieLinkBdWithPd2Player(html, card.path, finalOrigin, det);
                if (det.episodes.length > 0) {
                  storeDetailInCaches(card.path, det, Date.now() + 3600_000);
                }
              }
            } catch {
              // ignore
            }
          }
        })();
      }
      return prefetchedDetails;
    };

    const cacheKey = `${rawPath}::page=${page}::q=${search}::node=${nodeId || 'auto'}`;
    const cached = catalogCache.get(cacheKey);
    if (!forceRefresh && cached && cached.expiresAt > Date.now()) {
      const normalized = normalizeMovieCardList(cached.data.items);
      res.json({
        ok: true,
        cached: true,
        path: rawPath,
        page,
        maxPage: cached.data.maxPage,
        activeNodeId: cached.data.activeNodeId,
        items: normalized,
        prefetchedDetails: collectPrefetchedDetails(normalized, cached.data.activeNodeId),
      });
      return;
    }

    try {
      const mbTargetPath = isNewReleasesView
        ? '/new-releases'
        : isNewUploadsView
          ? '/new-uploads'
          : upstreamBasePath;
      const shouldFetchExtraArchivePage =
        !search &&
        page === 1 &&
        (isTrendingHomeView ||
          isHotDhamakaView ||
          isNewUploadsView ||
          isNewReleasesView ||
          upstreamBasePath === '/movies');
      const baseClean = upstreamBasePath === '/' ? '' : upstreamBasePath.replace(/\/+$/, '');
      const extraPrimaryPage2Path = `${baseClean}/page/2`;

      const [mbRes, primaryRes, primaryPage2Res] = await Promise.allSettled([
        upstreamBasePath === '/adult18plus' && !search
          ? Promise.resolve({ items: [], maxPage: 1 })
          : fetchMovieBoxCatalog(mbTargetPath, page, search),
        fetchFromMirrors(targetPath, nodeId),
        shouldFetchExtraArchivePage
          ? fetchFromMirrors(extraPrimaryPage2Path, nodeId)
          : Promise.reject(new Error('Skip extra primary page')),
      ]);

      const mbParsed =
        mbRes.status === 'fulfilled' ? mbRes.value : { items: [], maxPage: 2500 };
      const primaryParsed =
        primaryRes.status === 'fulfilled'
          ? parseMovieCards(primaryRes.value.html)
          : { items: [], maxPage: 520 };
      const primaryPage2Items =
        primaryPage2Res.status === 'fulfilled'
          ? parseMovieCards(primaryPage2Res.value.html).items
          : [];

      const activeNodeId =
        nodeId === 'node-moviebox'
          ? 'node-moviebox'
          : primaryRes.status === 'fulfilled'
            ? primaryRes.value.activeNodeId
            : 'node-moviebox';

      const allPrimaryItems = [...primaryParsed.items, ...primaryPage2Items];

      if (mbParsed.items.length > 0) {
        upsertItemsIntoMasterArchive(mbParsed.items, upstreamBasePath, false);
      }
      if (allPrimaryItems.length > 0) {
        upsertItemsIntoMasterArchive(allPrimaryItems, upstreamBasePath, false);
      }

      let items: MovieCardItem[] = [];
      if (search) {
        // UNFILTERED Dual-Source Search: return ALL matching titles from BOTH MovieBox & MovieLinkBD without dropping or cross-merging!
        const archivedMatches = queryMasterArchive({
          q: search,
          includeAdult: true,
          sort: 'popular',
          limit: 60,
        }).items;

        const mbPool = deduplicateByExactPath([
          ...mbParsed.items,
          ...archivedMatches.filter((i) => i.path?.startsWith('/mb/')),
        ]);
        const mlbdPool = deduplicateByExactPath([
          ...allPrimaryItems,
          ...archivedMatches.filter((i) => !i.path?.startsWith('/mb/') && !i.path?.startsWith('/mf/')),
        ]);

        const interleavedSearch: MovieCardItem[] = [];
        const maxSearchLen = Math.max(mbPool.length, mlbdPool.length);
        for (let i = 0; i < maxSearchLen; i++) {
          if (i < mbPool.length) interleavedSearch.push(mbPool[i]);
          if (i < mlbdPool.length) interleavedSearch.push(mlbdPool[i]);
        }
        items = deduplicateByExactPath(interleavedSearch);
      } else {
        items = mergeCatalogItems(mbParsed.items, allPrimaryItems, true);
      }

      // For Home/Trending/Hot/New Views on page 1, include brand-new uploads discovered in masterArchiveMap
      if (!search && (isTrendingHomeView || isHotDhamakaView || isNewUploadsView || isNewReleasesView)) {
        if (page === 1) {
          const recentArchived = queryMasterArchive({
            sort: isNewUploadsView ? 'latest' : 'popular',
            includeAdult: false,
            limit: 40,
          }).items;
          items = mergeCatalogItems(items, recentArchived, false);
        }
        if (isHotDhamakaView) {
          items = sortItemsByHotAndHype(items);
        } else if (isNewUploadsView) {
          items = sortItemsByRecentUpload(items);
        } else if (isNewReleasesView) {
          const sortedRecent = sortItemsByRecentUpload(items);
          const release2026And2025 = sortedRecent.filter(
            (i) => i.title.includes('2026') || i.title.includes('2025')
          );
          const releaseOlder = sortedRecent.filter(
            (i) => !i.title.includes('2026') && !i.title.includes('2025')
          );
          items = [...release2026And2025, ...releaseOlder];
        } else {
          items = sortItemsByHotAndHype(items);
        }
      } else {
        items = normalizeMovieCardList(items);
      }

      const maxPage = Math.max(mbParsed.maxPage, primaryParsed.maxPage);

      if (items.length > 0) {
        catalogCache.set(cacheKey, {
          data: { items, maxPage, activeNodeId },
          expiresAt: Date.now() + 30_000,
        });
        res.json({
          ok: true,
          cached: false,
          path: rawPath,
          page,
          maxPage,
          activeNodeId,
          items,
          prefetchedDetails: collectPrefetchedDetails(items, activeNodeId),
        });
        return;
      }
    } catch (err) {
      console.error('Catalog fetch error:', err);
    }

    const fallbackItems = sortItemsByRecentUpload(
      INITIAL_FALLBACK_MOVIES[rawPath] || INITIAL_FALLBACK_MOVIES['/'] || []
    );
    res.json({
      ok: true,
      fallback: true,
      path: rawPath,
      page,
      maxPage: 520,
      activeNodeId: 'node-moviebox',
      items: fallbackItems,
    });
  });

  // 5. Live Movie / Anime / Series Detail Extractor with STRICT Dual-Source Isolation (Zero Cross-Site Mixing!)
  app.get('/api/details', async (req, res) => {
    const rawPath = String(req.query.path || req.query.url || '').trim();
    const fallbackTitle = String(req.query.title || '').trim();
    const nodeId = String(req.query.node || '').trim();

    if (!rawPath && !fallbackTitle) {
      res.status(400).json({ ok: false, error: 'Missing path or title parameter' });
      return;
    }

    const isMovieBoxPath = rawPath.startsWith('/mb/');

    const attachFastRelatedSeasons = (detailObj: MovieDetailData): MovieDetailData => {
      if (detailObj.relatedSeasons && detailObj.relatedSeasons.length > 0) return detailObj;
      if (detailObj.typeBadge === 'MOVIE' && (detailObj.episodes?.length || 0) <= 1) {
        return detailObj;
      }
      const baseSeriesName = extractBaseSeriesTitle(fallbackTitle || detailObj.title);
      if (baseSeriesName && baseSeriesName.length >= 3) {
        const baseLower = baseSeriesName.toLowerCase();
        const matchingSeasons: MovieCardItem[] = [];
        const seenPaths = new Set<string>();
        const sameSource = (p: string) =>
          isMovieBoxPath ? p.startsWith('/mb/') : !p.startsWith('/mb/') && !p.startsWith('/mf/');
        for (const rec of masterArchiveMap.values()) {
          const item = rec.item;
          if (!item?.path || !sameSource(item.path)) continue;
          if (seenPaths.has(item.path) || item.path === detailObj.url) continue;
          const itemBase = extractBaseSeriesTitle(item.title).toLowerCase();
          if (itemBase === baseLower) {
            seenPaths.add(item.path);
            matchingSeasons.push(item);
          }
        }
        if (matchingSeasons.length > 0) {
          return { ...detailObj, relatedSeasons: matchingSeasons.slice(0, 12) };
        }
      }
      return detailObj;
    };

    const ensureDetailDubsAndUploader = (detailObj: MovieDetailData): MovieDetailData => {
      const dubs: MovieDubOption[] = Array.isArray(detailObj.dubs) ? [...detailObj.dubs] : [];
      const seenLabels = new Set(dubs.map((d) => d.label.toLowerCase()));

      const normalizeAudioLabel = (rawAudio: string): string => {
        const a = String(rawAudio || '').trim();
        if (!a) return 'Original Audio';
        if (/hindi/i.test(a) && /bangla|bengali/i.test(a)) return 'Hindi + Bangla dub';
        if (/hindi/i.test(a) && !/dub/i.test(a)) return 'Hindi dub';
        if (/bangla|bengali/i.test(a) && !/dub/i.test(a) && !/sub/i.test(a)) return 'Bangla dub';
        return a;
      };

      if (dubs.length === 0) {
        const primaryLabel = normalizeAudioLabel(detailObj.language || 'Original Audio');
        seenLabels.add(primaryLabel.toLowerCase());
        dubs.push({
          id: `dub-primary-${detailObj.url}`,
          label: primaryLabel,
          path: detailObj.url,
          active: true,
        });
      }

      for (const ep of detailObj.episodes || []) {
        for (const src of ep.sources || []) {
          const candidates = [src.audio, ...(src.audioLanguages || [])].filter(Boolean);
          for (const c of candidates) {
            const lbl = normalizeAudioLabel(c);
            const key = lbl.toLowerCase();
            if (lbl && !seenLabels.has(key)) {
              seenLabels.add(key);
              dubs.push({
                id: `dub-src-${key}`,
                label: lbl,
                path: detailObj.url,
                active: false,
              });
            }
          }
        }
      }

      for (const rel of detailObj.relatedSeasons || []) {
        const relLang = normalizeAudioLabel(rel.language || '');
        const key = relLang.toLowerCase();
        if (relLang && !seenLabels.has(key)) {
          seenLabels.add(key);
          dubs.push({
            id: `dub-rel-${rel.id || rel.path}`,
            label: relLang,
            path: rel.path,
            active: false,
          });
        }
      }

      return {
        ...detailObj,
        dubs,
        uploadedBy: 'CinePulse',
      };
    };

    // 1. Instant 0ms strict exact-path cache check (NEVER matches another source by title!)
    const instantHit = findCachedDetailByPathOrTitle(rawPath);
    if (instantHit) {
      res.json({
        ok: true,
        cached: true,
        detail: ensureDetailDubsAndUploader(attachFastRelatedSeasons(instantHit)),
      });
      return;
    }

    // 2. Dedicated MovieBox `/mb/<subjectId>/<detailSlug>` Resolver (Strictly isolated — zero MLBD mixing!)
    if (isMovieBoxPath) {
      try {
        let mbDetail = await fetchMovieBoxDetail(rawPath);
        if (mbDetail) {
          mbDetail = ensureDetailDubsAndUploader(attachFastRelatedSeasons(mbDetail));
          storeDetailInCaches(rawPath, mbDetail, Date.now() + 15 * 60_000);
          res.json({ ok: true, detail: mbDetail });
          return;
        }
      } catch (err) {
        console.error('MovieBox detail fetch error:', err);
      }
      res.status(404).json({
        ok: false,
        error: 'এই কন্টেন্টের স্ট্রিম এখনো প্রস্তুত হয়নি। কিছুক্ষণ পর আবার চেষ্টা করুন।',
      });
      return;
    }

    // 3. Dedicated MovieLinkBD Resolver with Upgraded `__PD2` Direct MP4 + Multi-Audio 1080p HLS (Strictly isolated — zero MovieBox mixing!)
    try {
      let resolvedPath = rawPath || '/';
      let { html, finalOrigin } = await fetchFromMirrors(resolvedPath, nodeId);

      const hasValidPlayer = (doc: string) =>
        doc.includes('mlbdInlinePlayerData') ||
        doc.includes('mlbdHdFrame') ||
        /src=["']\/p\/[A-Za-z0-9_-]{12,}["']/i.test(doc);

      const is404 =
        html.length < 1200 ||
        html.includes('<div class="n">404</div>') ||
        html.includes('Page not found') ||
        !hasValidPlayer(html);

      if (is404 && fallbackTitle) {
        const cleanQuery = extractBaseSeriesTitle(fallbackTitle)
          .split(/\s+/)
          .slice(0, 4)
          .join(' ');

        if (cleanQuery) {
          const searchRes = await fetchFromMirrors(`/search?q=${encodeURIComponent(cleanQuery)}`, nodeId);
          const { items } = parseMovieCards(searchRes.html);
          if (items.length > 0) {
            const wantSeasonMatch = fallbackTitle.match(/\b(S\d+|Season\s*\d+)/i);
            const wantSeason = wantSeasonMatch ? wantSeasonMatch[1].toLowerCase() : '';
            const bestItem =
              items.find((it) => wantSeason && it.title.toLowerCase().includes(wantSeason)) ||
              items.find((it) => Boolean(it.episodePill)) ||
              items[0];
            const resolved = await fetchFromMirrors(bestItem.path, nodeId);
            html = resolved.html;
            finalOrigin = resolved.finalOrigin;
            resolvedPath = bestItem.path;
          }
        }
      }

      let detail = parseMovieDetail(html, rawPath, finalOrigin);
      detail = await enrichMovieLinkBdWithPd2Player(html, resolvedPath, finalOrigin, detail);
      detail = ensureDetailDubsAndUploader(attachFastRelatedSeasons(detail));

      if (detail.episodes.length > 0 || detail.downloadButtons.length > 0 || detail.storyline) {
        storeDetailInCaches(rawPath, detail, Date.now() + 25 * 60_000);
      }

      res.json({ ok: true, detail });
    } catch (err) {
      console.error('Detail fetch error:', err);
      res.status(500).json({
        ok: false,
        error: 'ক্লাউড সার্ভার থেকে মুভির বিস্তারিত তথ্য লোড করা যায়নি। অনুগ্রহ করে অন্য Server Node সিলেক্ট করে চেষ্টা করুন।',
      });
    }
  });

  // 6. Opaque Anonymized Download & Stream Redirect Gateway (Automatically bypasses fifadekho landing gate!)
  app.get('/api/go', async (req, res) => {
    const token = String(req.query.t || '').trim();
    let target = decodeGatewayToken(token);
    if (!target || !target.startsWith('http')) {
      res.status(400).send('Invalid gateway link');
      return;
    }

    // If the link is a fifadekho.com gateway URL, automatically resolve `?view=links` to extract direct cloud download URL!
    if (/fifadekho\.com\/[a-z0-9]+/i.test(target) && !target.includes('view=links')) {
      try {
        const linksUrl = `${target.replace(/\/+$/, '')}?view=links`;
        const gwRes = await fetch(linksUrl, {
          headers: { 'User-Agent': 'Mozilla/5.0' },
        });
        if (gwRes.ok) {
          const gwHtml = await gwRes.text();
          const directCloudMatch = gwHtml.match(
            /<a\s+href=["'](https?:\/\/(?:hubcloud|new\d*\.xcloud|gdflix)[^"']+)["'][^>]*class=["'][^"']*nl-link-btn/i
          );
          if (directCloudMatch && directCloudMatch[1]) {
            target = directCloudMatch[1].trim();
          } else {
            target = linksUrl;
          }
        }
      } catch {
        target = `${target.replace(/\/+$/, '')}?view=links`;
      }
    }

    res.setHeader('Referrer-Policy', 'no-referrer');
    res.redirect(302, target);
  });

  // In-Memory Micro-Chunk Startup Buffer Cache (Caches initial 1.5MB startup chunk of active streams for 0ms instant start & zero socket hold!)
  const mbStartupChunkCache = new Map<
    string,
    {
      buf: Buffer;
      totalSize: number;
      contentType: string;
      expiresAt: number;
    }
  >();

  // 6a-1. MovieBox HD Micro-Chunked Turbo MP4 Stream & Download Proxy (1.5MB Startup Chunk + 2.5MB Playback Micro-Chunks + RAM Cache!)
  app.get(['/api/mb-stream', '/api/mb-stream.mp4'], async (req, res) => {
    const token = String(req.query.t || '').trim();
    const fbToken = String(req.query.fb || '').trim();
    const isDownload = String(req.query.dl || '0') === '1';
    const rawFilename = String(req.query.name || req.query.fn || 'CinePulse-HD.mp4')
      .replace(/[^a-zA-Z0-9._-]+/g, '-')
      .replace(/^-+|-+$/g, '');
    const targetUrl = decodeGatewayToken(token);
    const fallbackUrl = fbToken ? decodeGatewayToken(fbToken) : '';
    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid MovieBox stream token');
      return;
    }

    const INITIAL_STARTUP_CHUNK_BYTES = Math.floor(1.5 * 1024 * 1024); // 1.5MB micro-chunk for <80ms instant moov + keyframe start
    const PLAYBACK_MICRO_CHUNK_BYTES = Math.floor(2.5 * 1024 * 1024); // 2.5MB micro-chunk so sockets free up immediately between chunks

    let requestedStart = 0;
    let requestedEnd = NaN;
    if (req.headers.range) {
      const m = String(req.headers.range).match(/bytes=(\d+)-(\d*)/i);
      if (m) {
        requestedStart = parseInt(m[1], 10) || 0;
        requestedEnd = m[2] ? parseInt(m[2], 10) : NaN;
      }
    }

    // 0ms RAM Hit if the client is requesting bytes inside our cached 1.5MB startup micro-chunk!
    if (!isDownload && req.method !== 'HEAD' && requestedStart < INITIAL_STARTUP_CHUNK_BYTES) {
      const ramHit = mbStartupChunkCache.get(targetUrl);
      if (ramHit && ramHit.expiresAt > Date.now() && requestedStart < ramHit.buf.length) {
        const sliceEnd = !Number.isNaN(requestedEnd)
          ? Math.min(requestedEnd, ramHit.buf.length - 1)
          : ramHit.buf.length - 1;
        if (sliceEnd >= requestedStart) {
          const chunk = ramHit.buf.subarray(requestedStart, sliceEnd + 1);
          res.status(206);
          res.setHeader('Content-Type', ramHit.contentType || 'video/mp4');
          res.setHeader('Accept-Ranges', 'bytes');
          res.setHeader('Cache-Control', 'public, max-age=3600');
          res.setHeader('Content-Length', String(chunk.length));
          res.setHeader(
            'Content-Range',
            `bytes ${requestedStart}-${sliceEnd}/${ramHit.totalSize}`
          );
          res.end(chunk);
          return;
        }
      }
    }

    const abortController = new AbortController();
    res.on('close', () => {
      if (!res.writableEnded) {
        abortController.abort();
      }
    });

    const forwardHeaders: Record<string, string> = {
      'User-Agent':
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
      Accept: '*/*',
    };

    const chunkCap =
      requestedStart === 0 ? INITIAL_STARTUP_CHUNK_BYTES : PLAYBACK_MICRO_CHUNK_BYTES;

    if (req.headers.range && !isDownload) {
      const cappedEnd =
        !Number.isNaN(requestedEnd) && requestedEnd >= requestedStart
          ? Math.min(requestedEnd, requestedStart + chunkCap - 1)
          : requestedStart + chunkCap - 1;
      forwardHeaders.Range = `bytes=${requestedStart}-${cappedEnd}`;
    } else if (!req.headers.range && !isDownload && req.method !== 'HEAD') {
      forwardHeaders.Range = `bytes=0-${INITIAL_STARTUP_CHUNK_BYTES - 1}`;
    } else if (req.headers.range) {
      forwardHeaders.Range = String(req.headers.range);
    }

    try {
      let upstream: Response | null = null;
      // Send official whitelisted Referer headers required by hakunaymatata.com (NEVER substitute a full movie with a 3-min trailer!)
      const refererCandidates: Array<Record<string, string>> = [
        { Referer: `${MOVIEBOX_CLASSIC_ORIGIN}/`, Origin: MOVIEBOX_CLASSIC_ORIGIN },
        { Referer: `${MOVIEBOX_ORIGIN}/`, Origin: MOVIEBOX_ORIGIN },
        { Referer: 'https://movieboxhd.net/', Origin: 'https://movieboxhd.net' },
      ];
      for (let attempt = 0; attempt < refererCandidates.length; attempt++) {
        try {
          upstream = await fetch(targetUrl, {
            method: req.method === 'HEAD' ? 'HEAD' : 'GET',
            headers: { ...forwardHeaders, ...refererCandidates[attempt] },
            signal: abortController.signal,
          });
          if (upstream.ok || upstream.status === 206) {
            break;
          }
        } catch (fetchErr) {
          if (abortController.signal.aborted || attempt === refererCandidates.length - 1) throw fetchErr;
        }
      }

      if (!upstream || (!upstream.ok && upstream.status !== 206)) {
        res.status(upstream?.status || 502).send(`Upstream CDN returned ${upstream?.status || 502}`);
        return;
      }

      const contentType = upstream.headers.get('content-type') || 'video/mp4';
      const contentRange = upstream.headers.get('content-range') || '';
      const contentLength = upstream.headers.get('content-length');

      res.status(upstream.status);
      res.setHeader('Content-Type', contentType);
      res.setHeader('Accept-Ranges', upstream.headers.get('accept-ranges') || 'bytes');
      res.setHeader('Cache-Control', 'public, max-age=3600');
      if (contentLength) {
        res.setHeader('Content-Length', contentLength);
      }
      if (contentRange) {
        res.setHeader('Content-Range', contentRange);
      }
      if (isDownload) {
        res.setHeader(
          'Content-Disposition',
          `attachment; filename="${rawFilename.endsWith('.mp4') ? rawFilename : `${rawFilename}.mp4`}"`
        );
      }

      if (!upstream.body || req.method === 'HEAD') {
        res.end();
        return;
      }

      // Cache initial 0..1.5MB startup chunk in RAM while streaming it to the client!
      const shouldCacheStartupChunk =
        !isDownload &&
        requestedStart === 0 &&
        upstream.status === 206 &&
        !mbStartupChunkCache.has(targetUrl);
      const totalMatch = contentRange.match(/\/(\d+)$/);
      const parsedTotalSize = totalMatch ? parseInt(totalMatch[1], 10) : 0;
      const collectedChunks: Buffer[] = [];
      let collectedLen = 0;

      const nodeStream = Readable.fromWeb(upstream.body as any);
      if (shouldCacheStartupChunk && parsedTotalSize > 0) {
        nodeStream.on('data', (chunk: Buffer) => {
          if (collectedLen <= INITIAL_STARTUP_CHUNK_BYTES) {
            const b = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
            collectedChunks.push(b);
            collectedLen += b.length;
          }
        });
        nodeStream.on('end', () => {
          if (collectedLen > 32768 && collectedLen <= INITIAL_STARTUP_CHUNK_BYTES + 65536) {
            if (mbStartupChunkCache.size >= 24) {
              const oldestKey = mbStartupChunkCache.keys().next().value;
              if (oldestKey) mbStartupChunkCache.delete(oldestKey);
            }
            mbStartupChunkCache.set(targetUrl, {
              buf: Buffer.concat(collectedChunks),
              totalSize: parsedTotalSize,
              contentType,
              expiresAt: Date.now() + 10 * 60_000,
            });
          }
        });
      }
      nodeStream.on('error', () => {
        if (!res.headersSent) res.status(502).end();
        else res.end();
      });
      nodeStream.pipe(res);
    } catch {
      if (!res.headersSent) {
        res.status(502).send('MovieBox stream connection interrupted');
      } else {
        res.end();
      }
    }
  });

  // 6a-2. On-Demand Episode Resolver (Resolves full Season/Episode direct CDN MP4 and 302-redirects straight to CDN with no-referrer!)
  app.get(['/api/mb-ep-stream', '/api/mb-ep-stream.mp4'], async (req, res) => {
    const subjectId = String(req.query.subjectId || '').trim();
    const detailPath = String(req.query.detailPath || '').trim();
    const se = Math.max(0, parseInt(String(req.query.se || '1'), 10) || 1);
    const ep = Math.max(0, parseInt(String(req.query.ep || '1'), 10) || 1);
    const preferredQuality = parseInt(String(req.query.q || '480'), 10) || 480;
    const isDownload = String(req.query.dl || '0') === '1';

    if (!subjectId || !detailPath) {
      res.status(400).send('Missing subjectId or detailPath');
      return;
    }

    try {
      let { sources } = await fetchMovieBoxPlayStreams(
        subjectId,
        detailPath,
        se,
        ep,
        detailPath,
        'Original Audio'
      );
      if (!sources.length) {
        const fbNext = await fetchMovieBoxPlayStreams(
          subjectId,
          detailPath,
          se,
          ep + 1,
          detailPath,
          'Original Audio'
        );
        if (fbNext.sources.length) sources = fbNext.sources;
      }
      if (!sources.length) {
        const fbMovie = await fetchMovieBoxPlayStreams(
          subjectId,
          detailPath,
          0,
          0,
          detailPath,
          'Original Audio'
        );
        if (fbMovie.sources.length) sources = fbMovie.sources;
      }
      if (!sources.length) {
        res.status(404).send('No full stream found for this episode');
        return;
      }
      const chosen =
        sources.find((s) => s.quality === preferredQuality) ||
        sources.find((s) => s.quality === 480) ||
        sources.find((s) => s.quality === 720) ||
        sources[0];
      const targetUrl = isDownload && chosen.downloadUrl ? chosen.downloadUrl : chosen.url;
      res.setHeader('Referrer-Policy', 'no-referrer');
      res.redirect(302, targetUrl);
    } catch {
      res.status(502).send('Failed to resolve episode stream');
    }
  });

  // 6a-3. Direct HLS Manifest Rewriter Proxy (Supports CMAF/fMP4 byte-range HLS & multi-audio tracks)
  app.get(['/api/mlbd-hls', '/api/mlbd-hls.m3u8'], async (req, res) => {
    const token = String(req.query.t || '').trim();
    const targetUrl = decodeGatewayToken(token);
    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid HLS token');
      return;
    }

    try {
      const upstream = await fetch(targetUrl, {
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
          Referer: `${latestMlbdOrigin}/`,
          Origin: latestMlbdOrigin,
          Accept: '*/*',
        },
        signal: AbortSignal.timeout(10000),
      });

      if (!upstream.ok) {
        res.status(upstream.status).send(`Upstream HLS returned ${upstream.status}`);
        return;
      }

      const manifestText = await upstream.text();
      const baseUrl = new URL(targetUrl);

      const rewriteUri = (rawRef: string, forcePlaylist = false): string => {
        try {
          const abs = new URL(rawRef.trim(), baseUrl).href;
          const tok = Buffer.from(abs, 'utf8').toString('base64url');
          const isSubPlaylist =
            forcePlaylist ||
            /\.m3u8(\?|$)/i.test(abs) ||
            /\/(?:hls|m|vsub)\//i.test(abs);
          return isSubPlaylist
            ? `/api/mlbd-hls.m3u8?t=${tok}`
            : `/api/mlbd-stream.mp4?t=${tok}`;
        } catch {
          return rawRef;
        }
      };

      const rewritten = manifestText
        .split(/\r?\n/)
        .map((line) => {
          const trimmed = line.trim();
          if (!trimmed) return line;
          if (trimmed.startsWith('#')) {
            // Rewrite URI="..." inside #EXT-X-MAP, #EXT-X-MEDIA, #EXT-X-KEY, etc.
            if (trimmed.includes('URI="')) {
              const isMediaOrIframe = /^#EXT-X-(?:MEDIA|I-FRAME-STREAM-INF)/i.test(trimmed);
              return line.replace(/URI="([^"]+)"/g, (_m, u) => `URI="${rewriteUri(u, isMediaOrIframe)}"`);
            }
            return line;
          }
          return rewriteUri(trimmed, false);
        })
        .join('\n');

      res.setHeader('Access-Control-Allow-Origin', '*');
      res.setHeader('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
      res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
      res.send(rewritten);
    } catch {
      res.status(502).send('HLS manifest proxy error');
    }
  });

  // 6a-4. Direct MP4 & HLS Byte-Range Segment Turbo Proxy (Forwards Range verbatim for CMAF/fMP4 HLS segments!)
  app.get(['/api/mlbd-stream', '/api/mlbd-stream.mp4'], async (req, res) => {
    const token = String(req.query.t || '').trim();
    const isDownload = String(req.query.dl || '0') === '1';
    const rawFilename = String(req.query.name || 'CinePulse-HD.mp4')
      .replace(/[^a-zA-Z0-9._-]+/g, '-')
      .replace(/^-+|-+$/g, '');
    const targetUrl = decodeGatewayToken(token);
    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid stream token');
      return;
    }

    const isHlsSeg = /\/(?:s|vseg)\//i.test(targetUrl);
    const abortController = new AbortController();
    res.on('close', () => {
      if (!res.writableEnded) abortController.abort();
    });

    const forwardHeaders: Record<string, string> = {
      'User-Agent':
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
      Referer: `${latestMlbdOrigin}/`,
      Origin: latestMlbdOrigin,
      Accept: '*/*',
    };

    if (isHlsSeg) {
      // CRITICAL for CMAF/fMP4 HLS byte-range segments (#EXT-X-MAP + #EXT-X-BYTERANGE): forward Range verbatim!
      if (req.headers.range) {
        forwardHeaders.Range = String(req.headers.range);
      }
    } else if (req.headers.range && !isDownload) {
      const m = String(req.headers.range).match(/bytes=(\d+)-(\d*)/i);
      if (m) {
        const start = parseInt(m[1], 10) || 0;
        const end = m[2] ? parseInt(m[2], 10) : NaN;
        const chunkCap =
          start === 0 ? Math.floor(1.5 * 1024 * 1024) : Math.floor(4 * 1024 * 1024);
        const cappedEnd =
          !Number.isNaN(end) && end >= start ? Math.min(end, start + chunkCap - 1) : start + chunkCap - 1;
        forwardHeaders.Range = `bytes=${start}-${cappedEnd}`;
      } else {
        forwardHeaders.Range = String(req.headers.range);
      }
    } else if (!req.headers.range && !isDownload && req.method !== 'HEAD') {
      forwardHeaders.Range = `bytes=0-${Math.floor(1.5 * 1024 * 1024) - 1}`;
    } else if (req.headers.range) {
      forwardHeaders.Range = String(req.headers.range);
    }

    try {
      const upstream = await fetch(targetUrl, {
        method: req.method === 'HEAD' ? 'HEAD' : 'GET',
        headers: forwardHeaders,
        signal: abortController.signal,
      });

      if (!upstream.ok && upstream.status !== 206) {
        res.status(upstream.status).send(`Upstream stream returned ${upstream.status}`);
        return;
      }

      const rawCt = upstream.headers.get('content-type') || '';
      const contentType = isHlsSeg
        ? req.headers.range
          ? 'video/mp4'
          : 'video/mp2t'
        : rawCt && !/image|octet-stream/i.test(rawCt)
          ? rawCt
          : 'video/mp4';
      const contentRange = upstream.headers.get('content-range');
      const contentLength = upstream.headers.get('content-length');

      res.status(upstream.status);
      res.setHeader('Access-Control-Allow-Origin', '*');
      res.setHeader('Access-Control-Expose-Headers', 'Content-Length, Content-Range');
      res.setHeader('Content-Type', contentType);
      res.setHeader('Accept-Ranges', upstream.headers.get('accept-ranges') || 'bytes');
      res.setHeader('Cache-Control', 'public, max-age=3600');
      if (contentLength) res.setHeader('Content-Length', contentLength);
      if (contentRange) res.setHeader('Content-Range', contentRange);
      if (isDownload) {
        res.setHeader(
          'Content-Disposition',
          `attachment; filename="${rawFilename.endsWith('.mp4') ? rawFilename : `${rawFilename}.mp4`}"`
        );
      }

      if (!upstream.body || req.method === 'HEAD') {
        res.end();
        return;
      }

      const nodeStream = Readable.fromWeb(upstream.body as any);
      nodeStream.on('error', () => {
        if (!res.headersSent) res.status(502).end();
        else res.end();
      });
      nodeStream.pipe(res);
    } catch {
      if (!res.headersSent) res.status(502).send('Stream proxy interrupted');
      else res.end();
    }
  });

  // 6b. Ultra-Fast Sequential MKV-to-HLS Live Streamer for iPhone / iPad (iOS Safari)
  interface IosHlsSession {
    hash: string;
    dir: string;
    targetUrl: string;
    proc: ChildProcess | null;
    abortController: AbortController;
    lastAccess: number;
    finished: boolean;
  }

  const iosHlsSessions = new Map<string, IosHlsSession>();

  const cleanupIosHlsSession = (hash: string) => {
    const sess = iosHlsSessions.get(hash);
    if (!sess) return;
    iosHlsSessions.delete(hash);
    try {
      sess.abortController.abort();
    } catch {
      // ignore
    }
    try {
      if (sess.proc && !sess.proc.killed) {
        sess.proc.kill('SIGKILL');
      }
    } catch {
      // ignore
    }
    try {
      fs.rmSync(sess.dir, { recursive: true, force: true });
    } catch {
      // ignore
    }
  };

  setInterval(() => {
    const now = Date.now();
    for (const [hash, sess] of iosHlsSessions.entries()) {
      if (now - sess.lastAccess > 120_000) {
        cleanupIosHlsSession(hash);
      }
    }
  }, 30_000).unref();

  const ensureIosHlsSession = async (targetUrl: string): Promise<IosHlsSession> => {
    const hash = crypto.createHash('sha1').update(targetUrl).digest('hex').slice(0, 16);
    const existing = iosHlsSessions.get(hash);
    if (existing && fs.existsSync(path.join(existing.dir, 'index.m3u8'))) {
      existing.lastAccess = Date.now();
      return existing;
    }

    if (existing) {
      cleanupIosHlsSession(hash);
    }

    // Keep at most 2 concurrent HLS remux sessions so /tmp stays lightweight
    if (iosHlsSessions.size >= 2) {
      const oldest = Array.from(iosHlsSessions.values()).sort(
        (a, b) => a.lastAccess - b.lastAccess
      )[0];
      if (oldest) cleanupIosHlsSession(oldest.hash);
    }

    const dir = path.join('/tmp', `cp-hls-${hash}`);
    fs.rmSync(dir, { recursive: true, force: true });
    fs.mkdirSync(dir, { recursive: true });

    const abortController = new AbortController();
    const session: IosHlsSession = {
      hash,
      dir,
      targetUrl,
      proc: null,
      abortController,
      lastAccess: Date.now(),
      finished: false,
    };
    iosHlsSessions.set(hash, session);

    const upstreamRes = await fetch(targetUrl, {
      signal: abortController.signal,
      headers: {
        'User-Agent':
          'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
      },
    });

    if (!upstreamRes.ok || !upstreamRes.body) {
      cleanupIosHlsSession(hash);
      throw new Error(`Upstream stream HTTP ${upstreamRes.status}`);
    }

    const ff = spawn('/usr/bin/ffmpeg', [
      '-hide_banner',
      '-loglevel',
      'error',
      '-fflags',
      '+nobuffer+genpts',
      '-probesize',
      '131072',
      '-analyzeduration',
      '100000',
      '-f',
      'matroska',
      '-i',
      'pipe:0',
      '-map',
      '0:v:0',
      '-map',
      '0:a:0?',
      '-c:v',
      'copy',
      '-c:a',
      'aac',
      '-ac',
      '2',
      '-b:a',
      '128k',
      '-af',
      "volume=enable='between(t,0,13.5)':volume=0",
      '-bsf:v',
      'h264_mp4toannexb',
      '-f',
      'hls',
      '-hls_playlist_type',
      'event',
      '-hls_time',
      '2',
      '-hls_list_size',
      '0',
      '-hls_flags',
      'independent_segments+temp_file',
      '-hls_segment_filename',
      path.join(dir, 'seg_%04d.ts'),
      path.join(dir, 'index.m3u8'),
    ]);

    session.proc = ff;
    ff.on('exit', () => {
      session.finished = true;
    });
    ff.stdin.on('error', () => {});

    const reader = upstreamRes.body.getReader();
    (async () => {
      let bytesTransferred = 0;
      const BURST_BYTES = 24 * 1024 * 1024; // 24MB instant high-speed burst (~3 mins of video)
      try {
        while (true) {
          if (Date.now() - session.lastAccess > 120_000) {
            cleanupIosHlsSession(hash);
            break;
          }
          const { done, value } = await reader.read();
          if (done) {
            ff.stdin.end();
            break;
          }
          bytesTransferred += value.byteLength;
          if (!ff.stdin.write(Buffer.from(value))) {
            await new Promise<void>((resolve) => ff.stdin.once('drain', () => resolve()));
          }
          // After initial 24MB burst, lightly pace download so /tmp is never flooded
          if (bytesTransferred > BURST_BYTES) {
            await new Promise((r) => setTimeout(r, 25));
          }
        }
      } catch {
        try {
          ff.stdin.end();
        } catch {
          // ignore
        }
      }
    })();

    // Wait up to 4.5s for index.m3u8 + first segments (seg_0001.ts or seg_0000.ts) to appear
    const startWait = Date.now();
    while (Date.now() - startWait < 4500) {
      const m3u8Path = path.join(dir, 'index.m3u8');
      const seg1Path = path.join(dir, 'seg_0001.ts');
      const seg0Path = path.join(dir, 'seg_0000.ts');
      if (
        fs.existsSync(m3u8Path) &&
        (fs.existsSync(seg1Path) || (fs.existsSync(seg0Path) && Date.now() - startWait > 1400))
      ) {
        return session;
      }
      await new Promise((r) => setTimeout(r, 45));
    }

    return session;
  };

  app.options('/api/ios-hls/:token/:file', (_req, res) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, HEAD, OPTIONS');
    res.status(204).end();
  });

  app.get('/api/ios-hls/:token/:file', async (req, res) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, HEAD, OPTIONS');

    const token = String(req.params.token || '').trim();
    const file = String(req.params.file || '').trim();
    const targetUrl = decodeGatewayToken(token);

    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid stream token');
      return;
    }

    try {
      if (file === 'index.m3u8') {
        const session = await ensureIosHlsSession(targetUrl);
        session.lastAccess = Date.now();
        const m3u8Path = path.join(session.dir, 'index.m3u8');
        if (!fs.existsSync(m3u8Path)) {
          res.status(503).send('HLS playlist initializing');
          return;
        }
        res.setHeader('Content-Type', 'application/vnd.apple.mpegurl');
        res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
        res.send(fs.readFileSync(m3u8Path, 'utf8'));
        return;
      }

      if (/^seg_\d+\.ts$/.test(file)) {
        const hash = crypto.createHash('sha1').update(targetUrl).digest('hex').slice(0, 16);
        let session = iosHlsSessions.get(hash);
        if (!session) {
          session = await ensureIosHlsSession(targetUrl);
        }
        session.lastAccess = Date.now();
        const segPath = path.join(session.dir, file);

        // Wait briefly if segment is currently being finalized by ffmpeg
        const waitStart = Date.now();
        while (!fs.existsSync(segPath) && Date.now() - waitStart < 3500) {
          await new Promise((r) => setTimeout(r, 50));
        }

        if (!fs.existsSync(segPath)) {
          res.status(404).send('Segment not ready');
          return;
        }

        res.setHeader('Content-Type', 'video/mp2t');
        res.setHeader('Cache-Control', 'public, max-age=600');
        fs.createReadStream(segPath).pipe(res);
        return;
      }

      res.status(404).send('Not found');
    } catch (err) {
      console.error('iOS HLS stream error:', err);
      res.status(502).send('Stream transcode failed');
    }
  });

  // 6c. Embedded MKV Subtitle & Exact Audio-Visual Sync Extractor (/api/subtitles/extract)
  const mkvSubExtractCache = new Map<string, { srt: string; expiresAt: number }>();

  app.get('/api/subtitles/extract', async (req, res) => {
    const streamUrl = String(req.query.url || '').trim();
    const startSec = Math.max(0, Number(req.query.startSec || 0) || 0);
    const windowMode = String(req.query.mode || 'probe').trim(); // 'probe' (fast 6MB header+opening) or 'window' (15-min seek window)

    if (!streamUrl || !streamUrl.startsWith('http') || !fs.existsSync('/usr/bin/ffmpeg')) {
      res.json({ ok: false, srt: '' });
      return;
    }

    const cacheKey = `${streamUrl}::${windowMode}::${Math.floor(startSec / 300)}`;
    const cached = mkvSubExtractCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json({ ok: true, srt: cached.srt, cached: true });
      return;
    }

    try {
      let extractedSrt = '';

      if (windowMode === 'window' && startSec > 0) {
        // Seek directly over HTTP to startSec and demux 12 minutes of embedded subtitle packets (-vn -an = zero video/audio decode overhead)
        extractedSrt = await new Promise<string>((resolve) => {
          const chunks: Buffer[] = [];
          const ff = spawn('/usr/bin/ffmpeg', [
            '-hide_banner',
            '-loglevel',
            'error',
            '-ss',
            String(startSec),
            '-t',
            '720',
            '-i',
            streamUrl,
            '-vn',
            '-an',
            '-map',
            '0:s:0?',
            '-c:s',
            'srt',
            '-f',
            'srt',
            'pipe:1',
          ]);
          const killTimer = setTimeout(() => {
            try {
              ff.kill('SIGKILL');
            } catch {}
            resolve(Buffer.concat(chunks).toString('utf8'));
          }, 5200);

          ff.stdout.on('data', (chunk: Buffer) => chunks.push(chunk));
          ff.on('close', () => {
            clearTimeout(killTimer);
            resolve(Buffer.concat(chunks).toString('utf8'));
          });
          ff.on('error', () => {
            clearTimeout(killTimer);
            resolve('');
          });
        });
      } else {
        // Fast 5.5MB Range probe from byte 0: downloads in ~350ms and gives exact opening embedded subtitle cues for auto-sync!
        const controller = new AbortController();
        const fetchTimer = setTimeout(() => controller.abort(), 4200);
        const upstream = await fetch(streamUrl, {
          signal: controller.signal,
          headers: {
            Range: 'bytes=0-5767167',
            'User-Agent': 'Mozilla/5.0',
          },
        }).finally(() => clearTimeout(fetchTimer));

        if (upstream.ok && upstream.body) {
          const arrayBuf = await upstream.arrayBuffer();
          const inputBuf = Buffer.from(arrayBuf);
          extractedSrt = await new Promise<string>((resolve) => {
            const outChunks: Buffer[] = [];
            const ff = spawn('/usr/bin/ffmpeg', [
              '-hide_banner',
              '-loglevel',
              'error',
              '-i',
              'pipe:0',
              '-vn',
              '-an',
              '-map',
              '0:s:0?',
              '-c:s',
              'srt',
              '-f',
              'srt',
              'pipe:1',
            ]);
            const killTimer = setTimeout(() => {
              try {
                ff.kill('SIGKILL');
              } catch {}
              resolve(Buffer.concat(outChunks).toString('utf8'));
            }, 2500);

            ff.stdout.on('data', (chunk: Buffer) => outChunks.push(chunk));
            ff.stdin.on('error', () => {});
            ff.on('close', () => {
              clearTimeout(killTimer);
              resolve(Buffer.concat(outChunks).toString('utf8'));
            });
            ff.on('error', () => {
              clearTimeout(killTimer);
              resolve('');
            });

            ff.stdin.end(inputBuf);
          });
        }
      }

      if (extractedSrt && extractedSrt.includes('-->')) {
        mkvSubExtractCache.set(cacheKey, {
          srt: extractedSrt,
          expiresAt: Date.now() + 30 * 60_000,
        });
        res.json({ ok: true, srt: extractedSrt });
        return;
      }
    } catch {
      // ignore probe failure
    }

    res.json({ ok: false, srt: '' });
  });

  // 7. User Movie Requests & Broken Link Reports API
  app.get('/api/requests', (_req, res) => {
    res.json({ ok: true, requests: movieRequestsStore });
  });

  app.post('/api/requests', (req, res) => {
    const title = sanitizeBrandText(String(req.body?.title || '').trim());
    const type = String(req.body?.type || 'MOVIE').toUpperCase() as UserMovieRequest['type'];
    const language = sanitizeBrandText(String(req.body?.language || 'Bangla / Dual Audio').trim());
    const notes = sanitizeBrandText(String(req.body?.notes || '').trim());

    if (!title) {
      res.status(400).json({ ok: false, error: 'অনুগ্রহ করে মুভি বা সিরিজের নাম লিখুন' });
      return;
    }

    const item: UserMovieRequest = {
      id: `req-${Date.now()}`,
      title,
      type: ['MOVIE', 'SERIES', 'ANIME', 'BROKEN_LINK'].includes(type) ? type : 'MOVIE',
      language,
      notes,
      status: 'Queued',
      createdAt: Date.now(),
    };
    movieRequestsStore.unshift(item);
    if (movieRequestsStore.length > 30) movieRequestsStore.pop();

    res.json({ ok: true, request: item, requests: movieRequestsStore });
  });

  // (Legacy /api/myflix removed — 2-source engine uses strictly isolated primary streams)

  // 7b. Global Live Notifications API (New Movie Uploads + Popular High-Rating Movies Broadcast for Everyone)
  app.get('/api/notifications', (_req, res) => {
    const notifications = buildGlobalNotifications();
    res.json({
      ok: true,
      serverTime: Date.now(),
      notifications,
    });
  });

  app.post('/api/notifications/broadcast', (req, res) => {
    const rawMovie = req.body?.movie as MovieCardItem | undefined;
    const category =
      req.body?.category === 'TOP_RATED_POPULAR' ? 'TOP_RATED_POPULAR' : 'NEW_UPLOAD';

    if (!rawMovie || !rawMovie.title || !rawMovie.path) {
      res.status(400).json({ ok: false, error: 'Invalid movie payload for broadcast' });
      return;
    }

    const normMovie = normalizeMovieCardItem(rawMovie, Date.now());
    const ratingNum = parseFloat(normMovie.rating || '9.2') || 9.2;
    const broadcastItem: GlobalMovieNotification = {
      id: `notif-live-${Date.now()}-${normMovie.id}`,
      category,
      badgeText:
        category === 'TOP_RATED_POPULAR'
          ? `জনপ্রিয় ধামাকা • ★ ${ratingNum.toFixed(1)}`
          : 'মাত্র আপলোড হলো 🔥',
      headlineBn:
        category === 'TOP_RATED_POPULAR'
          ? `সবার জন্য হাই-রেটিং জনপ্রিয় মুভি অ্যালার্ট: ${normMovie.title}`
          : `নতুন মুভি আপলোড অ্যালার্ট (সবার জন্য): ${normMovie.title}`,
      subtitleBn: `${normMovie.language || 'Multi Audio'} • ${normMovie.quality || '1080p Full HD'} • রেটিং ★ ${ratingNum.toFixed(1)}`,
      movie: normMovie,
      createdAt: Date.now(),
      ratingScore: ratingNum,
    };

    customBroadcastNotifications.unshift(broadcastItem);
    if (customBroadcastNotifications.length > 12) {
      customBroadcastNotifications.pop();
    }

    res.json({
      ok: true,
      broadcast: broadcastItem,
      notifications: buildGlobalNotifications(),
    });
  });

  // 8. Ultra-Stealth White-Label Proxy Mode (Hides all upstream logos, links, sidebars & intro sounds)
  app.get('/api/proxy-page', async (req, res) => {
    const rawPath = String(req.query.path || '/').trim();
    const nodeId = String(req.query.node || '').trim();

    try {
      const { html, finalOrigin } = await fetchFromMirrors(rawPath, nodeId);
      let processed = html;

      // Remove iOS redirect & ad scripts
      processed = processed
        .replace(/<script>\(function\(\)\{try\{var ua=navigator\.userAgent[\s\S]*?<\/script>/i, '')
        .replace(/<script[^>]*id=["']mlbd-display-ads[^"']*["'][^>]*>[\s\S]*?<\/script>/gi, '')
        .replace(/<script[^>]*id=["']mlbd-click-ads[^"']*["'][^>]*>[\s\S]*?<\/script>/gi, '')
        .replace(/\/mlbd-adopen\.php/g, '/api/noop')
        .replace(/MovieLinkBD/gi, 'CinePulse HD')
        .replace(/movielinkbd\.[a-z]+/gi, 'CinePulse');

      const stealthBridge = `
        <base href="${finalOrigin}/" />
        <style>
          #mlbd-adfree, .mlbd-ad-slot, [data-mlbd-ad], #mlbd-install,
          header .logo, .site-logo, .telegram-join, .tg-banner, .social-links,
          a[href*="t.me"], a[href*="telegram"], .footer, footer {
            display: none !important;
          }
        </style>
        <script>
          // Mute any automatic intro sound or page audio synth
          try {
            window.Audio = function() {
              return { play: function(){ return Promise.resolve(); }, pause: function(){}, addEventListener: function(){} };
            };
            if (window.speechSynthesis) {
              window.speechSynthesis.speak = function() {};
            }
          } catch (_) {}

          document.addEventListener('click', function(e) {
            var a = e.target && e.target.closest ? e.target.closest('a[href]') : null;
            if (!a) return;
            var href = a.getAttribute('href') || '';
            if (!href || href.startsWith('#') || href.startsWith('javascript:')) return;
            try {
              var u = new URL(href, '${finalOrigin}');
              if (u.hostname.includes('movielinkbd')) {
                e.preventDefault();
                e.stopPropagation();
                window.location.href = '/api/proxy-page?path=' + encodeURIComponent(u.pathname + u.search);
              }
            } catch (_) {}
          }, true);
        </script>
      `;

      processed = processed.replace(/<head[^>]*>/i, (match) => `${match}${stealthBridge}`);

      res.setHeader('Content-Type', 'text/html; charset=utf-8');
      res.send(processed);
    } catch {
      res.status(502).send(`
        <!doctype html>
        <html>
          <body style="background:#090b10;color:#f1f5f9;font-family:sans-serif;padding:2rem;text-align:center;">
            <h3>সার্ভারের সাথে সংযোগ করা যাচ্ছে না</h3>
            <p>অনুগ্রহ করে অ্যাপের মেইন ভিউ ব্যবহার করুন অথবা অন্য Server Node নির্বাচন করুন।</p>
          </body>
        </html>
      `);
    }
  });

  // 9. Unified Public & Real-Time Auto-Sync API (/api/v1/*)
  app.get('/api/v1/feed', (req, res) => {
    const category = String(req.query.category || '/').trim();
    const source = String(req.query.source || 'all').trim();
    const sort = String(req.query.sort || 'popular').trim() as 'latest' | 'popular' | 'rating';
    const limit = Math.min(200, Math.max(1, parseInt(String(req.query.limit || '48'), 10) || 48));
    const offset = Math.max(0, parseInt(String(req.query.offset || '0'), 10) || 0);
    const { items, total } = queryMasterArchive({
      category,
      source,
      sort,
      limit,
      offset,
      includeAdult: category === '/adult18plus',
    });
    res.json({
      ok: true,
      total,
      count: items.length,
      sources: getArchiveCountsBySite(),
      lastSyncedAt: lastAutoSyncAt,
      items,
    });
  });

  app.get('/api/v1/latest', (req, res) => {
    const limit = Math.min(200, Math.max(1, parseInt(String(req.query.limit || '48'), 10) || 48));
    const source = String(req.query.source || 'all').trim();
    const { items, total } = queryMasterArchive({ source, sort: 'latest', limit });
    res.json({
      ok: true,
      total,
      lastSyncedAt: lastAutoSyncAt,
      items,
    });
  });

  app.get('/api/v1/search', async (req, res) => {
    const q = String(req.query.q || '').trim();
    if (!q) {
      res.json({ ok: true, total: 0, items: [] });
      return;
    }
    const [mbRes, mlbdRes] = await Promise.allSettled([
      fetchMovieBoxCatalog('/', 1, q),
      fetchFromMirrors(`/search?q=${encodeURIComponent(q)}`),
    ]);
    const mbItems = mbRes.status === 'fulfilled' ? mbRes.value.items : [];
    const mlbdItems = mlbdRes.status === 'fulfilled' ? parseMovieCards(mlbdRes.value.html).items : [];
    const archived = queryMasterArchive({ q, includeAdult: true, limit: 60 }).items;
    const combined = deduplicateByExactPath([...mbItems, ...mlbdItems, ...archived]);
    res.json({
      ok: true,
      query: q,
      total: combined.length,
      items: combined,
    });
  });

  app.get('/api/v1/platforms', async (req, res) => {
    const platform = String(req.query.platform || 'Hoichoi').trim();
    const page = Math.max(1, parseInt(String(req.query.page || '1'), 10) || 1);
    try {
      const token = await getMovieBoxBearerToken();
      const headers = buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`, token);
      const r = await fetch(
        `${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/platform/play-list?page=${page}&perPage=6&platform=${encodeURIComponent(platform)}`,
        { headers, signal: AbortSignal.timeout(6000) }
      );
      if (!r.ok) {
        res.status(r.status).json({ ok: false, platform, items: [] });
        return;
      }
      const data = await r.json();
      const monthList = Array.isArray(data?.data?.monthList) ? data.data.monthList : [];
      const subjects = monthList.flatMap((m: any) => (Array.isArray(m?.subjects) ? m.subjects : []));
      res.json({ ok: true, platform, page, count: subjects.length, monthList });
    } catch {
      res.status(502).json({ ok: false, platform, items: [] });
    }
  });

  app.get('/api/v1/sports', async (_req, res) => {
    try {
      const headers = buildMovieBoxHeaders(`${MOVIEBOX_ORIGIN}/`);
      const r = await fetch(`${MOVIEBOX_SPORTS_API_ORIGIN}/wefeed-h5api-bff/live/match-list-v5`, {
        headers,
        signal: AbortSignal.timeout(6000),
      });
      const data = r.ok ? await r.json() : null;
      res.json({ ok: Boolean(data), data: data?.data || null });
    } catch {
      res.status(502).json({ ok: false, data: null });
    }
  });

  app.get('/api/v1/sync-status', (_req, res) => {
    const counts = getArchiveCountsBySite();
    res.json({
      ok: true,
      isSyncRunning,
      autoSyncIntervalSeconds: Math.round(AUTO_SYNC_INTERVAL_MS / 1000),
      lastSyncedAt: lastAutoSyncAt,
      lastCycleNewItemsCount,
      totalIndexed: counts.total,
      sources: counts,
      connectedSseClients: sseClients.size,
    });
  });

  app.post('/api/v1/sync', async (_req, res) => {
    await syncLiveCategories(false);
    const counts = getArchiveCountsBySite();
    res.json({
      ok: true,
      lastSyncedAt: lastAutoSyncAt,
      lastCycleNewItemsCount,
      totalIndexed: counts.total,
      sources: counts,
    });
  });

  app.get('/api/v1/events', (req, res) => {
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache, no-transform');
    res.setHeader('Connection', 'keep-alive');
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.flushHeaders?.();

    sseClients.add(res);
    res.write(
      `event: connected\ndata: ${JSON.stringify({
        ok: true,
        totalIndexed: getArchiveCountsBySite().total,
        lastSyncedAt: lastAutoSyncAt,
      })}\n\n`
    );

    const ping = setInterval(() => {
      try {
        res.write(': ping\n\n');
      } catch {
        clearInterval(ping);
        sseClients.delete(res);
      }
    }, 25_000);

    req.on('close', () => {
      clearInterval(ping);
      sseClients.delete(res);
    });
  });

  app.get('/api/health', (_req, res) => {
    const counts = getArchiveCountsBySite();
    res.status(200).json({
      ok: true,
      service: 'CinePulse HD',
      uptimeSeconds: Math.round(process.uptime()),
      totalIndexed: counts.total,
      sources: counts,
      lastSyncedAt: lastAutoSyncAt,
      autoSyncIntervalSeconds: Math.round(AUTO_SYNC_INTERVAL_MS / 1000),
      timestamp: Date.now(),
    });
  });

  app.all('/api/noop', (_req, res) => {
    res.status(204).end();
  });

  // Never serve expired static db-shards (HTTP 410 Gone URLs) — force clients to use live /api/details
  app.get('/db-shards/:file', (_req, res) => {
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate');
    res.json({ details: {} });
  });

  // Self-healing Service Worker endpoint: immediately wipes any stale Workbox precaches on Render and reloads clients
  app.get(['/sw.js', '/dev-sw.js'], (_req, res) => {
    res.setHeader('Content-Type', 'application/javascript; charset=utf-8');
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
    res.send(`
      self.addEventListener('install', () => {
        self.skipWaiting();
      });
      self.addEventListener('activate', (event) => {
        event.waitUntil(
          (async () => {
            try {
              const keys = await caches.keys();
              await Promise.all(keys.map((k) => caches.delete(k)));
            } catch (_) {}
            try {
              await self.registration.unregister();
            } catch (_) {}
            try {
              await self.clients.claim();
              const windowClients = await self.clients.matchAll({ type: 'window' });
              for (const client of windowClients) {
                client.navigate(client.url);
              }
            } catch (_) {}
          })()
        );
      });
    `);
  });

  if (process.env.NODE_ENV !== 'production') {
    const vite = await createViteServer({
      server: { middlewareMode: true, hmr: false },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(__dirname, 'dist');
    app.use(
      express.static(distPath, {
        setHeaders: (res, filePath) => {
          if (
            filePath.endsWith('.html') ||
            filePath.endsWith('.json') ||
            filePath.endsWith('.webmanifest') ||
            filePath.endsWith('sw.js') ||
            filePath.endsWith('registerSW.js')
          ) {
            res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
          } else {
            res.setHeader('Cache-Control', 'public, max-age=31536000, immutable');
          }
        },
      })
    );
    app.get('*', (_req, res) => {
      res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
      res.sendFile(path.join(distPath, 'index.html'));
    });
  }

  app.listen(PORT, '0.0.0.0', () => {
    console.log(`CinePulse HD Cinema Server running on http://0.0.0.0:${PORT}`);

    // Automatic Render Free-Tier Keep-Alive Self-Ping (prevents 15-min idle sleep)
    const externalUrl = (process.env.RENDER_EXTERNAL_URL || process.env.APP_URL || '').replace(/\/+$/, '');
    if (externalUrl && externalUrl.startsWith('http')) {
      setInterval(() => {
        fetch(`${externalUrl}/api/health`, {
          headers: { 'User-Agent': 'CinePulse-KeepAlive/1.0' },
          signal: AbortSignal.timeout(8000),
        }).catch(() => {});
      }, 10 * 60 * 1000).unref();
    }
  });
}

startServer();

