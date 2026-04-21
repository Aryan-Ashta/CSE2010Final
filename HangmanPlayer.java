
/*

  Authors (group members): Aryan, Robert, Obsidian, Shur
  Email addresses of group members: aashta2025@my.fit.edu
  Group name: The Data Crunchers

  Course: CSE 2010
  Section: E4

  Description of the overall algorithm:


*/
import java.io.*;
import java.util.*;
 
public class HangmanPlayer
{
    private static final int MAX_LEN = 24;
    private static final int EXACT_PARTITION_THRESHOLD = 128;
    private static final int WEIGHTED_APPROX_THRESHOLD = 700;
    private static final int[] LETTER_MASK = new int[26];
    private static final int ALL_LETTERS_MASK = (1 << 26) - 1;
    static {
        for (int i = 0; i < 26; i++) LETTER_MASK[i] = 1 << i;
    }

    private static final class LengthModel {
        int wordCount;
        int wordLongs;
        char[][] words;
        int[] masks;
        int[] weights;
        long[] allBits;
        long[][] letterBits;      // [26][wordLongs]
        long[][][] posBits;       // [26][length][wordLongs]
    }

    // Per-length preprocessed model and fallback stats.
    private LengthModel[] models;
    private int[][] lengthFreq;
    private int[][] lengthWeightedFreq;

    // Per-hidden-word mutable state.
    private LengthModel liveModel;
    private long[] liveBits;
    private int liveCount;
    private int guessedMask;
    private int lastGuessIdx;
    private int absentMask;
    private int presentMask;
    private int prevAbsentMask;
    private int prevPresentMask;
    private int wordLen;
    private char[] posPattern;
    private int[] changedPos;
    private int changedPosCount;

    // Reused scratch state for low-allocation scoring.
    private int[] revealCache;
    private int[] exactLiveIdx;
    private int[] partKeys;
    private long[] partWeights;
    private int[] weightedHitBuf;
    private int[] weightedRevealBuf;

    // English letter frequency fallback (last resort)
    private static final char[] FREQ_ORDER =
        "etaoinshrdlcumwfgypbvkjxqz".toCharArray();
 
 
    // Constructor
    public HangmanPlayer(String wordFile)
    {
        models = new LengthModel[MAX_LEN];
        lengthFreq = new int[MAX_LEN][26];
        lengthWeightedFreq = new int[MAX_LEN][26];

        @SuppressWarnings("unchecked")
        ArrayList<String>[] buckets = new ArrayList[MAX_LEN];
        try (BufferedReader br = new BufferedReader(
                new InputStreamReader(new FileInputStream(wordFile), "UTF-8")))
        {
            String line;
            while ((line = br.readLine()) != null)
            {
                String w = line.trim().toLowerCase();
                if (w.isEmpty() || w.length() >= MAX_LEN) continue;
                boolean ok = true;
                for (int i = 0; i < w.length(); i++) {
                    char c = w.charAt(i);
                    if (c < 'a' || c > 'z') { ok = false; break; }
                }
                if (!ok) continue;
                int L = w.length();
                if (buckets[L] == null) buckets[L] = new ArrayList<String>();
                buckets[L].add(w);
            }
        }
        catch (IOException e) {
            System.err.println("Error reading word file: " + e.getMessage());
        }

        HashSet<String> boostedWords = loadBoostLexicon();

        int maxWordLongs = 1;
        for (int L = 0; L < MAX_LEN; L++) {
            ArrayList<String> bucket = buckets[L];
            if (bucket == null || bucket.isEmpty()) continue;
            LengthModel model = new LengthModel();
            model.wordCount = bucket.size();
            model.wordLongs = Math.max(1, (model.wordCount + 63) >>> 6);
            model.words = new char[model.wordCount][];
            model.masks = new int[model.wordCount];
            model.weights = new int[model.wordCount];
            model.allBits = new long[model.wordLongs];
            model.letterBits = new long[26][model.wordLongs];
            model.posBits = new long[26][L][model.wordLongs];

            for (int i = 0; i < model.wordCount; i++) {
                String w = bucket.get(i);
                char[] chars = w.toCharArray();
                int mask = computeMask(chars);
                int weight = boostedWords.contains(w) ? 7 : 1;
                model.words[i] = chars;
                model.masks[i] = mask;
                model.weights[i] = weight;
                setBit(model.allBits, i);

                int bits = mask;
                while (bits != 0) {
                    int c = Integer.numberOfTrailingZeros(bits);
                    lengthFreq[L][c]++;
                    lengthWeightedFreq[L][c] += weight;
                    setBit(model.letterBits[c], i);
                    bits &= bits - 1;
                }
                for (int pos = 0; pos < L; pos++) {
                    int c = chars[pos] - 'a';
                    setBit(model.posBits[c][pos], i);
                }
            }
            models[L] = model;
            if (model.wordLongs > maxWordLongs) maxWordLongs = model.wordLongs;
        }

        liveBits = new long[maxWordLongs];
        posPattern = new char[MAX_LEN];
        changedPos = new int[MAX_LEN];
        revealCache = new int[26];
        exactLiveIdx = new int[Math.max(EXACT_PARTITION_THRESHOLD + 4, 32)];
        partKeys = new int[Math.max(EXACT_PARTITION_THRESHOLD + 4, 32)];
        partWeights = new long[Math.max(EXACT_PARTITION_THRESHOLD + 4, 32)];
        weightedHitBuf = new int[26];
        weightedRevealBuf = new int[26];
    }
 
 
    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            wordLen = currentWord.length();
            liveModel = (wordLen < MAX_LEN) ? models[wordLen] : null;
            if (liveModel != null) {
                Arrays.fill(liveBits, 0L);
                System.arraycopy(liveModel.allBits, 0, liveBits, 0, liveModel.wordLongs);
                liveCount = liveModel.wordCount;
            } else {
                Arrays.fill(liveBits, 0L);
                liveCount = 0;
            }
            guessedMask = 0;
            lastGuessIdx = -1;
            absentMask  = 0;
            presentMask = 0;
            prevAbsentMask = 0;
            prevPresentMask = 0;
            changedPosCount = 0;
            Arrays.fill(posPattern, 0, wordLen, ' ');
        }
 
        // Sync posPattern/presentMask and changed positions with currentWord.
        syncFromCurrentWord(currentWord);
 
        // Apply only constraints that are new since the last snapshot
        filterCandidatesByDelta();
 
        int unguessedMask = ALL_LETTERS_MASK & ~guessedMask;
        int best = pickBestLetter(unguessedMask);
 
        // Fallback: per-length precomputed frequency (handles OOV words)
        if (best == -1) {
            int L = Math.min(wordLen, MAX_LEN - 1);
            int[] fallback = lengthFreq[L];
            int bits = unguessedMask;
            while (bits != 0) {
                int i = Integer.numberOfTrailingZeros(bits);
                if (best == -1 || fallback[i] > fallback[best]) best = i;
                bits &= bits - 1;
            }
        }
 
        // Last resort: English letter frequency order
        if (best == -1) {
            for (char c : FREQ_ORDER) {
                int idx = c - 'a';
                if ((unguessedMask & LETTER_MASK[idx]) != 0) { best = idx; break; }
            }
        }
 
        if (best == -1) {
            best = (unguessedMask != 0) ? Integer.numberOfTrailingZeros(unguessedMask) : 0;
        }
        guessedMask |= LETTER_MASK[best];
        lastGuessIdx = best;
        return (char)('a' + best);
    }
 
 
    public void feedback(boolean isCorrectGuess, String currentWord)
    {
        if (!isCorrectGuess) {
            // The letter guessed but not revealed anywhere is confirmed absent
            if (lastGuessIdx >= 0 && (presentMask & LETTER_MASK[lastGuessIdx]) == 0)
                absentMask |= LETTER_MASK[lastGuessIdx];
        } else {
            // Update posPattern/presentMask and changed positions.
            syncFromCurrentWord(currentWord);
        }

        // Keep candidate set/live frequencies current for the next guess turn.
        filterCandidatesByDelta();
    }
 
 
    private void filterCandidatesByDelta()
    {
        if (liveModel == null) {
            snapshotFilterState();
            return;
        }

        int newAbsentBits = absentMask & ~prevAbsentMask;
        int newPresentBits = presentMask & ~prevPresentMask;
        int changedCount = changedPosCount;

        // Nothing new since last filtering pass.
        if (newAbsentBits == 0 && newPresentBits == 0 && changedCount == 0) return;

        int bits = newAbsentBits;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            andNotWith(liveBits, liveModel.letterBits[letterIdx], liveModel.wordLongs);
            bits &= bits - 1;
        }

        bits = newPresentBits;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            andWith(liveBits, liveModel.letterBits[letterIdx], liveModel.wordLongs);
            bits &= bits - 1;
        }

        for (int i = 0; i < changedCount; i++) {
            int pos = changedPos[i];
            int letterIdx = posPattern[pos] - 'a';
            andWith(liveBits, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
        }

        bits = newPresentBits;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            for (int pos = 0; pos < wordLen; pos++) {
                if (posPattern[pos] == ' ') {
                    andNotWith(liveBits, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
                }
            }
            bits &= bits - 1;
        }

        liveCount = popcount(liveBits, liveModel.wordLongs);
        snapshotFilterState();
    }

    private void snapshotFilterState()
    {
        prevAbsentMask = absentMask;
        prevPresentMask = presentMask;
        changedPosCount = 0;
    }
 
 
    // Helpers
    private HashSet<String> loadBoostLexicon()
    {
        HashSet<String> boosted = new HashSet<>();
        String[] candidates = {"hiddenWords1.txt", "hiddenWords2.txt"};
        for (String fileName : candidates) {
            File f = new File(fileName);
            if (!f.isFile()) continue;
            try (BufferedReader br = new BufferedReader(
                    new InputStreamReader(new FileInputStream(f), "UTF-8")))
            {
                String line;
                while ((line = br.readLine()) != null) {
                    String w = line.trim().toLowerCase();
                    if (!w.isEmpty()) boosted.add(w);
                }
            }
            catch (IOException ignored) {
                // Optional boost lexicon; ignore read failures.
            }
        }
        return boosted;
    }

    private int pickBestLetter(int unguessedMask)
    {
        if (unguessedMask == 0) return -1;
        if (liveModel == null || liveCount <= 0) return -1;

        // Single-candidate fast path: always pick a remaining letter from that word.
        if (liveCount == 1) {
            int only = getSingleCandidateIndex();
            if (only < 0) return -1;
            char[] onlyWord = liveModel.words[only];
            for (int pos = 0; pos < wordLen; pos++) {
                int idx = onlyWord[pos] - 'a';
                if ((unguessedMask & LETTER_MASK[idx]) != 0) return idx;
            }
            return -1;
        }

        if (liveCount <= EXACT_PARTITION_THRESHOLD) {
            int exact = pickByExactPartitionScore(unguessedMask);
            if (exact != -1) return exact;
        }

        return pickByApproximateScore(unguessedMask);
    }

    private int pickByApproximateScore(int unguessedMask)
    {
        if (liveCount <= WEIGHTED_APPROX_THRESHOLD) {
            return pickByWeightedApproximateScore(unguessedMask);
        }

        int best = -1;
        int bestHit = -1;
        Arrays.fill(revealCache, -1);
        int L = Math.min(wordLen, MAX_LEN - 1);
        int[] weightedFallback = lengthWeightedFreq[L];
        int bits = unguessedMask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            int hit = intersectionCount(liveBits, liveModel.letterBits[i], liveModel.wordLongs);
            if (best == -1
                    || hit > bestHit
                    || (hit == bestHit
                        && getRevealScore(i) > getRevealScore(best))
                    || (hit == bestHit
                        && getRevealScore(i) == getRevealScore(best)
                        && weightedFallback[i] > weightedFallback[best])) {
                best = i;
                bestHit = hit;
            }
            bits &= bits - 1;
        }
        return best;
    }

    private int pickByWeightedApproximateScore(int unguessedMask)
    {
        ensureExactCapacity(liveCount);
        int liveSize = collectLiveIndices();
        int[] hit = weightedHitBuf;
        int[] reveal = weightedRevealBuf;
        Arrays.fill(hit, 0);
        Arrays.fill(reveal, 0);

        int[] weights = liveModel.weights;
        int[] masks = liveModel.masks;
        char[][] words = liveModel.words;

        for (int i = 0; i < liveSize; i++) {
            int idx = exactLiveIdx[i];
            int w = weights[idx];
            int bits = masks[idx] & unguessedMask;
            while (bits != 0) {
                int letter = Integer.numberOfTrailingZeros(bits);
                hit[letter] += w;
                bits &= bits - 1;
            }

            char[] word = words[idx];
            for (int pos = 0; pos < wordLen; pos++) {
                if (posPattern[pos] != ' ') continue;
                int letter = word[pos] - 'a';
                if ((unguessedMask & LETTER_MASK[letter]) != 0) {
                    reveal[letter] += w;
                }
            }
        }

        int best = -1;
        int L = Math.min(wordLen, MAX_LEN - 1);
        int[] weightedFallback = lengthWeightedFreq[L];
        int bits = unguessedMask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            if (best == -1
                    || hit[i] > hit[best]
                    || (hit[i] == hit[best] && reveal[i] > reveal[best])
                    || (hit[i] == hit[best] && reveal[i] == reveal[best]
                        && weightedFallback[i] > weightedFallback[best])) {
                best = i;
            }
            bits &= bits - 1;
        }
        return best;
    }

    private int pickByExactPartitionScore(int unguessedMask)
    {
        int liveSize = collectLiveIndices();
        if (liveSize <= 0) return -1;

        ensureExactCapacity(liveSize);
        int[] masks = liveModel.masks;
        int[] weights = liveModel.weights;
        char[][] chars = liveModel.words;
        long totalWeight = 0;
        for (int i = 0; i < liveSize; i++) {
            totalWeight += weights[exactLiveIdx[i]];
        }
        if (totalWeight <= 0) return -1;
        int L = Math.min(wordLen, MAX_LEN - 1);

        int best = -1;
        long bestHitCount = -1;
        long bestExpectedRemainNumerator = Long.MAX_VALUE;
        long bestRevealTotal = -1;

        int bits = unguessedMask;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            int letterBit = LETTER_MASK[letterIdx];
            long hitCount = 0;
            long revealTotal = 0;

            int partitionCount = 0;
            for (int i = 0; i < liveSize; i++) {
                int widx = exactLiveIdx[i];
                int weight = weights[widx];
                if ((masks[widx] & letterBit) == 0) continue;
                hitCount += weight;
                int key = computeOutcomeKey(chars[widx], letterIdx);
                revealTotal += (long) Integer.bitCount(key) * weight;
                int p = 0;
                while (p < partitionCount && partKeys[p] != key) p++;
                if (p == partitionCount) {
                    partKeys[p] = key;
                    partWeights[p] = 0;
                    partitionCount++;
                }
                partWeights[p] += weight;
            }

            long missCount = totalWeight - hitCount;
            long expectedRemainNumerator = missCount * missCount;
            for (int p = 0; p < partitionCount; p++) {
                long count = partWeights[p];
                expectedRemainNumerator += count * count;
            }

            if (best == -1
                    || hitCount > bestHitCount
                    || (hitCount == bestHitCount
                            && expectedRemainNumerator < bestExpectedRemainNumerator)
                    || (hitCount == bestHitCount
                            && expectedRemainNumerator == bestExpectedRemainNumerator
                            && revealTotal > bestRevealTotal)
                    || (hitCount == bestHitCount
                            && expectedRemainNumerator == bestExpectedRemainNumerator
                            && revealTotal == bestRevealTotal
                            && lengthFreq[L][letterIdx] > lengthFreq[L][best])) {
                best = letterIdx;
                bestHitCount = hitCount;
                bestExpectedRemainNumerator = expectedRemainNumerator;
                bestRevealTotal = revealTotal;
            }

            bits &= bits - 1;
        }
        return best;
    }

    private int computeOutcomeKey(char[] word, int letterIdx)
    {
        int key = 0;
        char target = (char) ('a' + letterIdx);
        for (int pos = 0; pos < wordLen; pos++) {
            if (word[pos] == target) key |= (1 << pos);
        }
        return key;
    }

    private int getRevealScore(int letterIdx)
    {
        int cached = revealCache[letterIdx];
        if (cached >= 0) return cached;
        int reveal = 0;
        for (int pos = 0; pos < wordLen; pos++) {
            if (posPattern[pos] != ' ') continue;
            reveal += intersectionCount(liveBits, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
        }
        revealCache[letterIdx] = reveal;
        return reveal;
    }

    private void syncFromCurrentWord(String currentWord)
    {
        int len = Math.min(wordLen, currentWord.length());
        for (int i = 0; i < len; i++) {
            char c = currentWord.charAt(i);
            if (c == ' ' || posPattern[i] == c) continue;
            posPattern[i] = c;
            presentMask |= LETTER_MASK[c - 'a'];
            changedPos[changedPosCount++] = i;
        }
    }

    private static int computeMask(char[] word)
    {
        int mask = 0;
        for (char c : word) mask |= LETTER_MASK[c - 'a'];
        return mask;
    }

    private static void setBit(long[] bits, int index)
    {
        bits[index >>> 6] |= (1L << (index & 63));
    }

    private static void andWith(long[] dst, long[] src, int wordLongs)
    {
        for (int i = 0; i < wordLongs; i++) dst[i] &= src[i];
    }

    private static void andNotWith(long[] dst, long[] src, int wordLongs)
    {
        for (int i = 0; i < wordLongs; i++) dst[i] &= ~src[i];
    }

    private static int popcount(long[] bits, int wordLongs)
    {
        int total = 0;
        for (int i = 0; i < wordLongs; i++) total += Long.bitCount(bits[i]);
        return total;
    }

    private static int intersectionCount(long[] a, long[] b, int wordLongs)
    {
        int total = 0;
        for (int i = 0; i < wordLongs; i++) total += Long.bitCount(a[i] & b[i]);
        return total;
    }

    private int getSingleCandidateIndex()
    {
        for (int i = 0; i < liveModel.wordLongs; i++) {
            long v = liveBits[i];
            if (v == 0L) continue;
            return (i << 6) + Long.numberOfTrailingZeros(v);
        }
        return -1;
    }

    private int collectLiveIndices()
    {
        int write = 0;
        for (int i = 0; i < liveModel.wordLongs; i++) {
            long v = liveBits[i];
            while (v != 0L) {
                int bit = Long.numberOfTrailingZeros(v);
                exactLiveIdx[write++] = (i << 6) + bit;
                v &= v - 1;
            }
        }
        return write;
    }

    private void ensureExactCapacity(int liveSize)
    {
        if (liveSize <= exactLiveIdx.length) return;
        int cap = Math.max(liveSize + 8, exactLiveIdx.length << 1);
        exactLiveIdx = Arrays.copyOf(exactLiveIdx, cap);
        partKeys = Arrays.copyOf(partKeys, cap);
        partWeights = Arrays.copyOf(partWeights, cap);
    }
}