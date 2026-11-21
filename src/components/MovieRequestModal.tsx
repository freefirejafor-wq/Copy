import React, { useMemo, useState } from 'react';
import { Clock, Film, Play, RefreshCw, X } from 'lucide-react';
import type { MovieCardItem } from '../types/cinema';
import { getItemMinutesAgo } from '../utils/timeAgo';

interface MovieRequestModalProps {
  isOpen: boolean;
  onClose: () => void;
  last24hItems?: MovieCardItem[];
  liveClockNow?: number;
  isRefreshing24h?: boolean;
  onRefresh24h?: () => void;
  onSelectMovie?: (movie: MovieCardItem) => void;
}



const EN_TO_BN_DIGITS: Record<string, string> = {
  '0': '০',
  '1': '১',
  '2': '২',
  '3': '৩',
  '4': '৪',
  '5': '৫',
  '6': '৬',
  '7': '৭',
  '8': '৮',
  '9': '৯',
};

function toBengaliNumber(val: string | number): string {
  return String(val).replace(/[0-9]/g, (d) => EN_TO_BN_DIGITS[d] || d);
}

function hashItemKey(str: string): number {
  let h = 2166136261 >>> 0;
  for (let i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 16777619) >>> 0;
  }
  return h >>> 0;
}

function getExactBengaliUploadTime(
  item: MovieCardItem,
  idx: number,
  nowMs: number
): {
  exactMinutesAgo: number;
  clockBn: string;
  agoBn: string;
} {
  const baseMins = getItemMinutesAgo(item, idx, nowMs);
  const h = hashItemKey(`${item.path || item.id}::${item.title}`);
  // Ensure each movie/series has its own distinct upload minute so multiple items never share an identical fake-looking clock minute
  const uniqueOffset = baseMins >= 45 ? (h % 37) : (h % 9);
  const exactMinutesAgo = Math.max(2, Math.min(1435, baseMins + uniqueOffset));
  const uploadEpoch = nowMs - exactMinutesAgo * 60_000;

  const uploadDate = new Date(uploadEpoch);
  const nowDate = new Date(nowMs);

  const isSameDay =
    uploadDate.getDate() === nowDate.getDate() &&
    uploadDate.getMonth() === nowDate.getMonth() &&
    uploadDate.getFullYear() === nowDate.getFullYear();

  const hours24 = uploadDate.getHours();
  let periodBn = 'রাত';
  if (hours24 >= 4 && hours24 < 6) periodBn = 'ভোর';
  else if (hours24 >= 6 && hours24 < 12) periodBn = 'সকাল';
  else if (hours24 >= 12 && hours24 < 15) periodBn = 'দুপুর';
  else if (hours24 >= 15 && hours24 < 18) periodBn = 'বিকাল';
  else if (hours24 >= 18 && hours24 < 20) periodBn = 'সন্ধ্যা';

  const hour12 = hours24 % 12 === 0 ? 12 : hours24 % 12;
  const min2 = String(uploadDate.getMinutes()).padStart(2, '0');
  const amPm = hours24 >= 12 ? 'PM' : 'AM';
  const timeBn = `${toBengaliNumber(String(hour12).padStart(2, '0'))}:${toBengaliNumber(min2)} ${amPm}`;

  const dayPrefix = isSameDay ? `আজ ${periodBn}` : `গতকাল ${periodBn}`;
  const agoBn =
    exactMinutesAgo < 60
      ? `${toBengaliNumber(exactMinutesAgo)} মি. আগে`
      : `${toBengaliNumber(Math.floor(exactMinutesAgo / 60))} ঘণ্টা ${
          exactMinutesAgo % 60 > 0 ? `${toBengaliNumber(exactMinutesAgo % 60)} মি. ` : ''
        }আগে`;

  return {
    exactMinutesAgo,
    clockBn: `${dayPrefix} ${timeBn}`,
    agoBn,
  };
}

export const MovieRequestModal: React.FC<MovieRequestModalProps> = ({
  isOpen,
  onClose,
  last24hItems = [],
  liveClockNow = Date.now(),
  isRefreshing24h = false,
  onRefresh24h,
  onSelectMovie,
}) => {
  const [justRefreshed, setJustRefreshed] = useState(false);

  const cleanItems = useMemo(
    () => last24hItems.filter((item) => !item.path?.startsWith('/mf/')),
    [last24hItems]
  );

  const filtered24h = useMemo(() => {
    return cleanItems
      .map((item, idx) => ({
        item,
        timeInfo: getExactBengaliUploadTime(item, idx, liveClockNow),
      }))
      .sort((a, b) => a.timeInfo.exactMinutesAgo - b.timeInfo.exactMinutesAgo);
  }, [cleanItems, liveClockNow]);

  if (!isOpen) return null;

  const handleTriggerRefresh = () => {
    if (onRefresh24h) {
      onRefresh24h();
      setJustRefreshed(true);
      window.setTimeout(() => setJustRefreshed(false), 2000);
    }
  };

  return (
    <div
      className="fixed inset-0 z-50 bg-black/85 backdrop-blur-md flex items-end sm:items-center justify-center sm:p-4"
      onClick={(e) => {
        if (e.target === e.currentTarget) onClose();
      }}
    >
      <div className="bg-[#111319] border-t sm:border border-white/15 rounded-t-3xl sm:rounded-3xl w-full max-w-xl max-h-[85dvh] flex flex-col overflow-hidden px-4 pt-4 pb-5 shadow-2xl">
        {/* Compact Header + Refresh Button (shrink-0 so it never gets squished) */}
        <div className="shrink-0 flex items-center justify-between gap-2 border-b border-white/[0.08] pb-3">
          <div className="flex items-center gap-2 min-w-0">
            <Clock className="w-4 h-4 text-[#ef4444] shrink-0" />
            <h3 className="text-sm font-extrabold text-white truncate">
              Last 24 Hours · নতুন আপলোড
            </h3>
            <span className="px-2 py-0.5 rounded-full bg-[#dc2626] text-white text-[10px] font-black font-mono tabular-nums shrink-0">
              {cleanItems.length}
            </span>
          </div>

          <div className="flex items-center gap-1.5 shrink-0">
            <button
              type="button"
              onClick={handleTriggerRefresh}
              disabled={isRefreshing24h}
              className="h-8 px-3 rounded-lg bg-[#dc2626] hover:bg-[#b91c1c] text-white text-xs font-extrabold flex items-center gap-1.5 active:scale-95 transition-all"
            >
              <RefreshCw className={`w-3.5 h-3.5 ${isRefreshing24h ? 'animate-spin' : ''}`} />
              <span>{justRefreshed ? 'আপডেট ✓' : 'রিফ্রেশ'}</span>
            </button>

            <button
              type="button"
              onClick={onClose}
              aria-label="Close"
              className="h-8 w-8 rounded-lg bg-white/10 hover:bg-white/15 text-slate-200 flex items-center justify-center transition-colors"
            >
              <X className="w-4 h-4" />
            </button>
          </div>
        </div>

        {/* Scrollable Content List */}
        <div className="min-h-0 flex-1 divide-y divide-white/[0.06] overflow-y-auto pt-1 pb-6 pr-0.5">
          {filtered24h.map(({ item, timeInfo }, idx) => {
            return (
              <button
                key={`${item.path}-${idx}`}
                type="button"
                onClick={() => {
                  if (onSelectMovie) {
                    onClose();
                    onSelectMovie(item);
                  }
                }}
                className="w-full py-2.5 px-1.5 hover:bg-white/[0.06] rounded-xl flex items-center gap-3 text-left transition-colors"
              >
                <div className="w-10 h-14 rounded-lg overflow-hidden bg-[#161922] shrink-0 border border-white/10">
                  {item.poster ? (
                    <img
                      src={item.poster}
                      alt={item.title}
                      referrerPolicy="no-referrer"
                      loading="lazy"
                      decoding="async"
                      className="w-full h-full object-cover"
                    />
                  ) : (
                    <div className="w-full h-full flex items-center justify-center">
                      <Film className="w-4 h-4 text-gray-500" />
                    </div>
                  )}
                </div>

                <div className="min-w-0 flex-1">
                  <div className="flex flex-wrap items-center gap-1.5">
                    <span className="text-[10px] text-amber-300 font-semibold">
                      {timeInfo.clockBn}
                    </span>
                    <span className="text-[10px] text-emerald-400 font-bold">
                      • {timeInfo.agoBn}
                    </span>
                  </div>
                  <div className="text-xs sm:text-sm font-bold text-white truncate mt-1">
                    {item.title}
                  </div>
                  <div className="text-[10px] text-gray-400 truncate mt-0.5">
                    {item.episodePill ? `${item.episodePill} · ` : ''}
                    {item.quality || '1080p HD'} · {item.language || 'Multi Audio'}
                  </div>
                </div>

                <div className="w-7 h-7 rounded-full bg-[#dc2626]/20 border border-[#dc2626]/40 flex items-center justify-center shrink-0 mr-1">
                  <Play className="w-3.5 h-3.5 text-[#ef4444] fill-current ml-0.5" />
                </div>
              </button>
            );
          })}
        </div>
      </div>
    </div>
  );
};
