"use strict";
/**
 * CATS (Computer Aided Typing Software) - Node.js port of the CS61A cats_gui.py server.
 *
 * Locally implemented (ported from cats.py / cats_gui.py):
 *   POST /request_paragraph, /analyze, /autocorrect, /report_progress, /fastest_words
 *   GET  /favicon.ico, /favicon
 *
 * Proxied to the official multiplayer/leaderboard server (mirrors the Python
 * local client's forward_to_server / multiplayer_post behavior):
 *   /request_id (-> /provide_id), /request_match, /request_progress,
 *   /record_wpm, /check_on_leaderboard, /update_name,
 *   /check_leaderboard_eligibility, /request_wpm_challenge,
 *   /claim_wpm_challenge, /leaderboard, /translate_to_pig_latin
 */
const http = require("http");
const https = require("https");
const fs = require("fs");
const path = require("path");

const PORT = Number(process.env.PORT) || 8000;
const HOST = "0.0.0.0";
const REMOTE_SERVER = "https://cats.cs61a.org";
const ROOT = __dirname;
const PUBLIC_DIR = path.join(ROOT, "public");
const FAVICON_DIR = path.join(ROOT, "favicons");
const SIMILARITY_LIMIT = 2;

/* ------------------------------------------------------------------ */
/* Data loading (utils.lines_from_file)                                */
/* ------------------------------------------------------------------ */

function linesFromFile(p) {
  const content = fs.readFileSync(p, "utf8");
  const lines = content.split("\n").map((s) => s.trim());
  if (content.endsWith("\n")) lines.pop(); // match Python readlines() behavior
  return lines;
}

const PARAGRAPHS = linesFromFile(path.join(ROOT, "data", "sample_paragraphs.txt"));
const WORDS_LIST = linesFromFile(path.join(ROOT, "data", "words.txt"));
const WORDS_SET = new Set(WORDS_LIST);
const LETTER_SETS = WORDS_LIST.map((w) => [w, new Set(w)]);

/* ------------------------------------------------------------------ */
/* String utilities (utils.py)                                         */
/* ------------------------------------------------------------------ */

const PUNCTUATION = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~";
const PUNCT_SET = new Set(PUNCTUATION);

function lower(s) {
  return s.toLowerCase();
}

function removePunctuation(s) {
  let out = "";
  for (const ch of s.trim()) {
    if (!PUNCT_SET.has(ch)) out += ch;
  }
  return out;
}

function split(s) {
  return s.split(/\s+/).filter((w) => w.length > 0);
}

/* ------------------------------------------------------------------ */
/* cats.py core logic                                                  */
/* ------------------------------------------------------------------ */

function pick(paragraphs, select, k) {
  const ps = paragraphs.filter((p) => select(p));
  if (ps.length <= k) return "";
  return ps[k];
}

function about(subject) {
  const lowerSubject = subject.map((x) => lower(x));
  return (paragraph) => {
    const clean = split(removePunctuation(lower(paragraph)));
    return clean.some((c) => lowerSubject.includes(c));
  };
}

function round2(x) {
  return Math.round((x + Number.EPSILON) * 100) / 100;
}

function accuracy(typed, source) {
  const typedWords = split(typed);
  const sourceWords = split(source);
  if (typedWords.length === 0 && sourceWords.length === 0) return 100.0;
  if (typedWords.length === 0 || sourceWords.length === 0) return 0.0;
  let correct = 0;
  for (let i = 0; i < Math.min(typedWords.length, sourceWords.length); i++) {
    if (typedWords[i] === sourceWords[i]) correct += 1;
  }
  return round2((correct / typedWords.length) * 100);
}

function wpm(typed, elapsed) {
  if (elapsed <= 0) return 0.0;
  return round2((typed.length / (5 * elapsed)) * 60);
}

function autocorrect(typedWord, wordList, diffFunction, limit) {
  if (wordList.includes(typedWord)) return typedWord;
  let minDiff = limit + 1;
  let minDiffWord = typedWord;
  for (const w of wordList) {
    const diff = diffFunction(typedWord, w, limit);
    if (diff < minDiff) {
      minDiff = diff;
      minDiffWord = w;
    }
  }
  if (minDiff > limit) return typedWord;
  return minDiffWord;
}

function felineFixes(typed, source, limit) {
  if (limit < 0) return Infinity;
  if (typed.length === 0 || source.length === 0) return typed.length + source.length;
  if (typed[0] === source[0]) return felineFixes(typed.slice(1), source.slice(1), limit);
  return felineFixes(typed.slice(1), source.slice(1), limit - 1) + 1;
}

function minimumMewtations(typed, source, limit) {
  if (limit < 0) return Infinity;
  if (typed.length === 0 || source.length === 0) return typed.length + source.length;
  if (typed[0] === source[0]) {
    return minimumMewtations(typed.slice(1), source.slice(1), limit);
  }
  let transpose = Infinity;
  if (typed.length >= 2 && source.length >= 2) {
    if (typed[0] === source[1] && typed[1] === source[0]) {
      transpose = 1 + minimumMewtations(typed.slice(2), source.slice(2), limit - 1);
    }
  }
  const add = 1 + minimumMewtations(typed, source.slice(1), limit - 1);
  const remove = 1 + minimumMewtations(typed.slice(1), source, limit - 1);
  const substitute = 1 + minimumMewtations(typed.slice(1), source.slice(1), limit - 1);
  return Math.min(add, remove, substitute, transpose);
}

function finalDiff(typed, source, limit) {
  return minimumMewtations(typed, source, limit);
}

/* Phase 3: multiplayer helpers */

function computeProgress(typed, source) {
  let count = 0;
  for (let i = 0; i < Math.min(typed.length, source.length); i++) {
    if (typed[i] !== source[i]) break;
    count += 1;
  }
  return count / source.length;
}

function timePerWord(words, timestampsPerPlayer) {
  const times = timestampsPerPlayer.map((tpp) => {
    const perPlayer = [];
    for (let t = 0; t < tpp.length - 1; t++) perPlayer.push(tpp[t + 1] - tpp[t]);
    return perPlayer;
  });
  return { words, times };
}

function fastestWords(match) {
  const playerIndices = match.times.map((_, i) => i);
  const wordIndices = match.words.map((_, i) => i);
  const result = playerIndices.map(() => []);
  for (const wi of wordIndices) {
    let fastest = playerIndices[0];
    let best = match.times[fastest][wi];
    for (const pi of playerIndices) {
      if (match.times[pi][wi] < best) {
        best = match.times[pi][wi];
        fastest = pi;
      }
    }
    result[fastest].push(match.words[wi]);
  }
  return result;
}

/* ------------------------------------------------------------------ */
/* cats_gui.py autocorrect route helpers                               */
/* ------------------------------------------------------------------ */

function similar(w, v, n) {
  let intersect = 0;
  for (const ch of w) if (v.has(ch)) intersect += 1;
  return intersect >= w.size - n && intersect >= v.size - n;
}

function reformat(word, rawWord) {
  if (rawWord !== "" && /[A-Z]/.test(rawWord[0])) {
    word = word[0].toUpperCase() + word.slice(1).toLowerCase();
  }
  let first = 0;
  while (first < rawWord.length && PUNCT_SET.has(rawWord[first])) first += 1;
  let last = rawWord.length - 1;
  while (last > first && PUNCT_SET.has(rawWord[last])) last -= 1;
  if (rawWord !== word) {
    word = rawWord.slice(0, first) + word;
    word = word + rawWord.slice(last + 1);
  }
  return word;
}

function autocorrectRoute(rawWord) {
  const word = lower(removePunctuation(rawWord));
  if (WORDS_SET.has(word) || word === "") return rawWord;
  const letters = new Set(word);
  const candidates = LETTER_SETS.filter(([, s]) => similar(s, letters, SIMILARITY_LIMIT)).map(
    ([w]) => w
  );
  const guess = autocorrect(word, candidates, finalDiff, SIMILARITY_LIMIT);
  return reformat(guess, rawWord);
}

/* ------------------------------------------------------------------ */
/* Remote proxy (mirrors multiplayer_post / forward_to_server)         */
/* ------------------------------------------------------------------ */

function remotePost(remotePath, data) {
  return new Promise((resolve) => {
    const body = JSON.stringify(data);
    const url = new URL(REMOTE_SERVER + "/" + remotePath);
    const req = https.request(
      {
        method: "POST",
        hostname: url.hostname,
        path: url.pathname,
        headers: { "Content-Type": "application/json", "Content-Length": Buffer.byteLength(body) },
        timeout: 15000,
      },
      (res) => {
        let text = "";
        res.on("data", (chunk) => (text += chunk));
        res.on("end", () => {
          if (text.trim()) {
            try {
              resolve(JSON.parse(text));
            } catch {
              resolve(null);
            }
          } else {
            resolve(null);
          }
        });
      }
    );
    req.on("error", () => resolve(null));
    req.on("timeout", () => {
      req.destroy();
      resolve(null);
    });
    req.write(body);
    req.end();
  });
}

/* ------------------------------------------------------------------ */
/* Route handlers                                                      */
/* ------------------------------------------------------------------ */

function shuffle(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function faviconDataUri() {
  const files = fs.readdirSync(FAVICON_DIR);
  const chosen = files[Math.floor(Math.random() * files.length)];
  const data = fs.readFileSync(path.join(FAVICON_DIR, chosen));
  return "data:image/png;base64," + data.toString("base64");
}

// POST routes implemented locally (ported from cats_gui.py / cats.py)
const localRoutes = {
  "/request_paragraph": (data) => {
    const topics = data.topics || null;
    const paragraphs = shuffle(PARAGRAPHS);
    const select = topics ? about(topics) : () => true;
    return pick(paragraphs, select, 0);
  },

  "/analyze": (data) => {
    const typed = data.typed_text ?? data.typedText ?? "";
    const prompted = data.prompted_text ?? data.promptedText ?? "";
    const start = data.start_time ?? data.startTime ?? 0;
    const end = data.end_time ?? data.endTime ?? 0;
    return { wpm: wpm(typed, end - start), accuracy: accuracy(typed, prompted) };
  },

  "/autocorrect": (data) => autocorrectRoute(data.word ?? ""),

  "/report_progress": async (data) => {
    const typed = String(data.typed ?? "").split(/\s+/).filter(Boolean);
    const prompt = String(data.prompt ?? "").split(/\s+/).filter(Boolean);
    const progress = computeProgress(typed, prompt);
    await remotePost("set_progress", { id: data.id, progress });
    return progress;
  },

  "/fastest_words": async (data) => {
    const words = String(data.prompt ?? "").split(/\s+/).filter(Boolean);
    const targets = data.targets ?? [];
    const progress = await remotePost("request_all_progress", { targets });
    if (!Array.isArray(progress)) return [];
    const startTimes = progress.map((p) => p[0][1]);
    const timesPerPlayer = progress.map((ps, i) => ps.map((p) => p[1] - startTimes[i]));
    const match = timePerWord(words, timesPerPlayer);
    return fastestWords(match);
  },
};

// POST routes forwarded to the official server (local path -> remote path)
const proxiedRoutes = {
  "/request_id": "provide_id",
  "/request_match": "request_match",
  "/request_progress": "request_progress",
  "/record_wpm": "record_wpm",
  "/check_on_leaderboard": "check_on_leaderboard",
  "/update_name": "update_name",
  "/check_leaderboard_eligibility": "check_leaderboard_eligibility",
  "/request_wpm_challenge": "request_wpm_challenge",
  "/claim_wpm_challenge": "claim_wpm_challenge",
  "/leaderboard": "leaderboard",
  "/translate_to_pig_latin": "translate_to_pig_latin",
};

/* ------------------------------------------------------------------ */
/* HTTP server                                                         */
/* ------------------------------------------------------------------ */

const MIME_TYPES = {
  html: "text/html",
  css: "text/css",
  js: "application/javascript",
  json: "application/json",
  svg: "image/svg+xml",
  gif: "image/gif",
  ico: "image/x-icon",
  png: "image/png",
  jpg: "image/jpeg",
  jpeg: "image/jpeg",
  txt: "text/plain",
  map: "application/json",
  ttf: "font/ttf",
  woff: "font/woff",
  woff2: "font/woff2",
};

function sendJson(res, status, value) {
  const body = JSON.stringify(value === undefined ? null : value);
  res.writeHead(status, { "Content-Type": "application/json" });
  res.end(body);
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let raw = "";
    req.on("data", (chunk) => (raw += chunk));
    req.on("end", () => {
      try {
        resolve(raw ? JSON.parse(raw) : {});
      } catch (e) {
        reject(e);
      }
    });
    req.on("error", reject);
  });
}

function serveStatic(req, res, pathname) {
  if (pathname === "/favicon.ico" || pathname === "/favicon") {
    res.writeHead(200, { "Content-Type": "image/x-icon" });
    res.end(faviconDataUri());
    return;
  }
  let rel = decodeURIComponent(pathname);
  if (rel === "/") rel = "/index.html";
  const filePath = path.join(PUBLIC_DIR, path.normalize(rel).replace(/^([.][.][/\\])+/, ""));
  if (!filePath.startsWith(PUBLIC_DIR)) {
    res.writeHead(404);
    res.end();
    return;
  }
  fs.readFile(filePath, (err, content) => {
    if (err) {
      res.writeHead(404);
      res.end();
      return;
    }
    const ext = filePath.split(".").pop().toLowerCase();
    res.writeHead(200, { "Content-Type": MIME_TYPES[ext] || "application/octet-stream" });
    res.end(content);
  });
}

const server = http.createServer(async (req, res) => {
  const pathname = decodeURIComponent(req.url.split("?")[0]);

  if (req.method === "GET") {
    serveStatic(req, res, pathname);
    return;
  }

  if (req.method === "POST") {
    let data;
    try {
      data = await readBody(req);
    } catch {
      sendJson(res, 400, null);
      return;
    }

    if (localRoutes[pathname]) {
      try {
        const result = await localRoutes[pathname](data);
        sendJson(res, 200, result);
      } catch (e) {
        console.error(e);
        sendJson(res, 500, null);
      }
      return;
    }

    if (proxiedRoutes[pathname]) {
      const result = await remotePost(proxiedRoutes[pathname], data);
      if (result === null) {
        sendJson(res, 500, null);
      } else {
        sendJson(res, 200, result);
      }
      return;
    }

    sendJson(res, 404, null);
    return;
  }

  res.writeHead(405);
  res.end();
});

server.listen(PORT, HOST, () => {
  console.log(`CATS server listening on http://${HOST}:${PORT}`);
});
