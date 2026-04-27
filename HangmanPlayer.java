
/*

  Authors (group members): Aryan, Robert, Obsidian, Shur
  Email addresses of group members: aashta2025@my.fit.edu, rlautenschla2025@my.fit.edu, sgaikwad2025@my.fit.edu, 
  Group name: The Data Crunchers

  Course: CSE 2010
  Section: E4

  Description of the overall algorithm:
  Uses a three stage system to pick the best letter to guess
  Stage 1: precomputed values > fast and constant time guesses
  Stage 2: approxumate guessing > based on bitset intersections 
  Stage 3: exact guessing > simualtes the resulting candidate subset of each guess to pick the best guess
  Thresholds for each stage running are based on the variables at the top of the class


*/
import java.io.*;
import java.util.*;
 
public class HangmanPlayer
{
    // Tuning constants and shared letter-to-bit mappings.
    private static final int MAX_LEN = 24;
    private static final int EXACT_PARTITION_THRESHOLD = 12;
    private static final int WEIGHTED_APPROX_THRESHOLD = 64;
    private static final int FAST_FALLBACK_THRESHOLD = 112;
    private static final int[] LETTER_MASK = new int[26];
    private static final int ALL_LETTERS_MASK = (1 << 26) - 1;
    static {
        for (int i = 0; i < 26; i++) LETTER_MASK[i] = 1 << i;
    }

    // Packed index data for one specific word length.
    private static final class LengthModel {
        int wordCount;
        int wordLongs;
        char[][] words;
        int[] masks;
        long[] allBits;
        long[][] letterBits;      // [26][wordLongs]
        long[][][] posBits;       // [26][length][wordLongs]
    }

    // Per-length preprocessed model and fallback stats.
    private LengthModel[] models;
    private int[][] lengthFreq;
    private int[][] openingOrder;

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
    private int wordLenBucket;
    private char[] posPattern;
    private int unknownPosMask;
    private boolean feedbackStateSynced;
    private int[] changedPos;
    private int changedPosCount;

    // Reused scratch state for low-allocation scoring.
    private int[] revealCache;
    private int[] exactLiveIdx;
    private int[] exactOutcomeBuf;
    private int[] partHashKeys;
    private long[] partHashWeights;
    private int[] partHashStamps;
    private int[] partHashUsedSlots;
    private int partHashEpoch;
    private int[] weightedHitBuf;
    private int[] weightedRevealBuf;
    private long[] mergeScratch;

    // English letter frequency fallback 
    private static final char[] FREQ_ORDER =
        "etaoinshrdlcumwfgypbvkjxqz".toCharArray();
 
 
    // Constructor
    public HangmanPlayer(String wordFile)
    {
        models = new LengthModel[MAX_LEN];
        lengthFreq = new int[MAX_LEN][26];
        openingOrder = new int[MAX_LEN][26];

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

        int maxWordLongs = 1;
        int maxWordCount = 1;
        for (int L = 0; L < MAX_LEN; L++) {
            ArrayList<String> bucket = buckets[L];
            if (bucket == null || bucket.isEmpty()) continue;
            LengthModel model = new LengthModel();
            model.wordCount = bucket.size();
            model.wordLongs = Math.max(1, (model.wordCount + 63) >>> 6);
            model.words = new char[model.wordCount][];
            model.masks = new int[model.wordCount];
            model.allBits = new long[model.wordLongs];
            model.letterBits = new long[26][model.wordLongs];
            model.posBits = new long[26][L][model.wordLongs];

            for (int i = 0; i < model.wordCount; i++) {
                String w = bucket.get(i);
                char[] chars = w.toCharArray();
                int mask = computeMask(chars);
                model.words[i] = chars;
                model.masks[i] = mask;
                setBit(model.allBits, i);

                int bits = mask;
                while (bits != 0) {
                    int c = Integer.numberOfTrailingZeros(bits);
                    lengthFreq[L][c]++;
                    setBit(model.letterBits[c], i);
                    bits &= bits - 1;
                }
                for (int pos = 0; pos < L; pos++) {
                    int c = chars[pos] - 'a';
                    setBit(model.posBits[c][pos], i);
                }
            }
            buildOpeningOrder(L);
            models[L] = model;
            if (model.wordLongs > maxWordLongs) maxWordLongs = model.wordLongs;
            if (model.wordCount > maxWordCount) maxWordCount = model.wordCount;
        }

        liveBits = new long[maxWordLongs];
        posPattern = new char[MAX_LEN];
        changedPos = new int[MAX_LEN];
        revealCache = new int[26];
        int initialExactCapacity = Math.max(WEIGHTED_APPROX_THRESHOLD + 8, Math.min(maxWordCount, 512));
        exactLiveIdx = new int[initialExactCapacity];
        exactOutcomeBuf = new int[initialExactCapacity * 26];
        int initialHashCap = 128;
        partHashKeys = new int[initialHashCap];
        partHashWeights = new long[initialHashCap];
        partHashStamps = new int[initialHashCap];
        partHashUsedSlots = new int[initialHashCap];
        partHashEpoch = 1;
        weightedHitBuf = new int[26];
        weightedRevealBuf = new int[26];
        mergeScratch = new long[maxWordLongs];
    }
 
 
    // Chooses the next letter guess using staged scoring and fallbacks.
    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            wordLen = currentWord.length();
            wordLenBucket = Math.min(wordLen, MAX_LEN - 1);
            liveModel = (wordLen < MAX_LEN) ? models[wordLen] : null;
            if (liveModel != null) {
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
            feedbackStateSynced = true;
            changedPosCount = 0;
            unknownPosMask = (wordLen == 0) ? 0 : ((1 << wordLen) - 1);
            Arrays.fill(posPattern, 0, wordLen, ' ');
        }

        // Sync posPattern/presentMask and changed positions with currentWord.
        if (!feedbackStateSynced) syncFromCurrentWord(currentWord);
 
        // Apply only constraints that are new since the last snapshot
        filterCandidatesByDelta();
 
        int unguessedMask = ALL_LETTERS_MASK & ~guessedMask;
        int best = pickBestLetter(unguessedMask);
 
        // Fallback: per-length precomputed frequency (handles OOV words)
        if (best == -1) {
            int[] fallback = lengthFreq[wordLenBucket];
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
        feedbackStateSynced = false;
        return (char)('a' + best);
    }
 
 
    // Applies game feedback and updates candidate constraints/state.
    public void feedback(boolean isCorrectGuess, String currentWord)
    {
        // End-of-word feedback cannot influence future guesses for this word.
        if (unknownPosMask == 0) {
            snapshotFilterState();
            feedbackStateSynced = true;
            return;
        }

        if (!isCorrectGuess) {
            // The letter guessed but not revealed anywhere is confirmed absent
            if (lastGuessIdx >= 0 && (presentMask & LETTER_MASK[lastGuessIdx]) == 0)
                absentMask |= LETTER_MASK[lastGuessIdx];
        } else {
            // Update posPattern/presentMask and changed positions.
            syncFromCurrentWord(currentWord);
            if (unknownPosMask == 0) {
                snapshotFilterState();
                feedbackStateSynced = true;
                return;
            }
        }

        // Keep candidate set/live frequencies current for the next guess turn.
        filterCandidatesByDelta();
        feedbackStateSynced = true;
    }
 
 
    // Filters live candidates using only newly learned constraints.
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

        for (int i = 0; i < changedCount; i++) {
            int pos = changedPos[i];
            int letterIdx = posPattern[pos] - 'a';
            andWith(liveBits, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
        }

        int bits = newPresentBits;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            andWith(liveBits, liveModel.letterBits[letterIdx], liveModel.wordLongs);
            bits &= bits - 1;
        }

        bits = newAbsentBits;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            andNotWith(liveBits, liveModel.letterBits[letterIdx], liveModel.wordLongs);
            bits &= bits - 1;
        }

        bits = newPresentBits;
        if (bits != 0 && unknownPosMask != 0) {
            while (bits != 0) {
                int letterIdx = Integer.numberOfTrailingZeros(bits);
                int posBits = unknownPosMask;
                if (posBits != 0) {
                    // Build union of candidate words where this letter appears in any still-unknown slot.
                    int firstPos = Integer.numberOfTrailingZeros(posBits);
                    System.arraycopy(liveModel.posBits[letterIdx][firstPos], 0, mergeScratch, 0, liveModel.wordLongs);
                    posBits &= posBits - 1;
                    while (posBits != 0) {
                        int pos = Integer.numberOfTrailingZeros(posBits);
                        orInto(mergeScratch, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
                        posBits &= posBits - 1;
                    }
                }
                // Remove words that place an already-revealed letter in hidden positions.
                andNotWith(liveBits, mergeScratch, liveModel.wordLongs);
                bits &= bits - 1;
            }
        }

        liveCount = popcount(liveBits, liveModel.wordLongs);
        snapshotFilterState();
    }

    // Saves current constraint masks as the new filtering baseline.
    private void snapshotFilterState()
    {
        prevAbsentMask = absentMask;
        prevPresentMask = presentMask;
        changedPosCount = 0;
    }
 
 
    // Helpers
    // Precomputes a strongest-first letter order for this word length.
    private void buildOpeningOrder(int L)
    {
        for (int i = 0; i < 26; i++) openingOrder[L][i] = i;
        for (int i = 0; i < 25; i++) {
            int best = i;
            for (int j = i + 1; j < 26; j++) {
                if (lengthFreq[L][openingOrder[L][j]] > lengthFreq[L][openingOrder[L][best]]) {
                    best = j;
                }
            }
            int tmp = openingOrder[L][i];
            openingOrder[L][i] = openingOrder[L][best];
            openingOrder[L][best] = tmp;
        }
    }

    // Routes to the best scoring strategy for current candidate size.
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

        // Speed-first shortcut: skip expensive live-bitset intersections while candidate
        // space is still very large; use strong per-length weighted priors first.
        if (liveCount >= FAST_FALLBACK_THRESHOLD) {
            if (presentMask == 0) {
                int opening = pickOpeningLetter(unguessedMask);
                if (opening != -1) return opening;
            }
            return pickByLengthFallback(unguessedMask);
        }

        if (liveCount <= EXACT_PARTITION_THRESHOLD) {
            int exact = pickByExactPartitionScore(unguessedMask);
            if (exact != -1) return exact;
        }

        return pickByApproximateScore(unguessedMask);
    }

    // Picks by per-length letter frequency when deep scoring is skipped.
    private int pickByLengthFallback(int unguessedMask)
    {
        int[] weightedFallback = lengthFreq[wordLenBucket];
        int best = -1;
        int bits = unguessedMask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            if (best == -1 || weightedFallback[i] > weightedFallback[best]) best = i;
            bits &= bits - 1;
        }
        return best;
    }

    // Scores letters with fast approximate metrics on the live set.
    private int pickByApproximateScore(int unguessedMask)
    {
        if (liveCount <= WEIGHTED_APPROX_THRESHOLD) {
            // When candidate count is modest, compute hit/reveal counts directly for better tie breaks.
            return pickByWeightedApproximateScore(unguessedMask);
        }

        int best = -1;
        int bestHit = -1;
        int bestReveal = -1;
        int[] weightedFallback = lengthFreq[wordLenBucket];
        int tieMask = 0;
        int bits = unguessedMask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            int hit = intersectionCount(liveBits, liveModel.letterBits[i], liveModel.wordLongs);
            if (best == -1
                    || hit > bestHit
                    || (hit == bestHit && weightedFallback[i] > weightedFallback[best])) {
                best = i;
                bestHit = hit;
                tieMask = LETTER_MASK[i];
            } else if (hit == bestHit) {
                tieMask |= LETTER_MASK[i];
            }
            bits &= bits - 1;
        }

        if ((tieMask & (tieMask - 1)) != 0) {
            // Break equal-hit ties by expected number of newly revealed positions.
            precomputeRevealScores(tieMask);
            bits = tieMask;
            while (bits != 0) {
                int i = Integer.numberOfTrailingZeros(bits);
                int reveal = revealCache[i];
                if (best == -1
                        || reveal > bestReveal
                        || (reveal == bestReveal
                            && weightedFallback[i] > weightedFallback[best])) {
                    best = i;
                    bestReveal = reveal;
                }
                bits &= bits - 1;
            }
        }
        return best;
    }

    // Uses direct live-word counting for tighter approximate tie-breaks.
    private int pickByWeightedApproximateScore(int unguessedMask)
    {
        ensureExactCapacity(liveCount);
        int liveSize = collectLiveIndices();
        int[] hit = weightedHitBuf;
        int[] reveal = weightedRevealBuf;
        Arrays.fill(hit, 0);
        Arrays.fill(reveal, 0);

        int[] masks = liveModel.masks;
        char[][] words = liveModel.words;

        for (int i = 0; i < liveSize; i++) {
            int idx = exactLiveIdx[i];
            int bits = masks[idx] & unguessedMask;
            while (bits != 0) {
                int letter = Integer.numberOfTrailingZeros(bits);
                hit[letter]++;
                bits &= bits - 1;
            }

            char[] word = words[idx];
            int posBits = unknownPosMask;
            while (posBits != 0) {
                int pos = Integer.numberOfTrailingZeros(posBits);
                int letter = word[pos] - 'a';
                if ((unguessedMask & LETTER_MASK[letter]) != 0) {
                    reveal[letter]++;
                }
                posBits &= posBits - 1;
            }
        }

        int best = -1;
        int bestHit = -1;
        int bestReveal = -1;
        int tieMask = 0;
        int[] weightedFallback = lengthFreq[wordLenBucket];
        int bits = unguessedMask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            if (best == -1
                    || hit[i] > bestHit
                    || (hit[i] == bestHit && reveal[i] > bestReveal)
                    || (hit[i] == bestHit && reveal[i] == bestReveal
                        && weightedFallback[i] > weightedFallback[best])) {
                best = i;
                bestHit = hit[i];
                bestReveal = reveal[i];
                tieMask = LETTER_MASK[i];
            } else if (hit[i] == bestHit && reveal[i] == bestReveal) {
                tieMask |= LETTER_MASK[i];
            }
            bits &= bits - 1;
        }

        if ((tieMask & (tieMask - 1)) != 0) {
            bits = tieMask;
            while (bits != 0) {
                int i = Integer.numberOfTrailingZeros(bits);
                if (best == -1
                        || weightedFallback[i] > weightedFallback[best]) {
                    best = i;
                }
                bits &= bits - 1;
            }
        }
        return best;
    }

    // Returns the highest-priority opening letter still unguessed.
    private int pickOpeningLetter(int unguessedMask)
    {
        int[] order = openingOrder[wordLenBucket];
        for (int i = 0; i < 26; i++) {
            int letter = order[i];
            if ((unguessedMask & LETTER_MASK[letter]) != 0) return letter;
        }
        return -1;
    }

    // Evaluates exact partition quality for small candidate sets.
    private int pickByExactPartitionScore(int unguessedMask)
    {
        int liveSize = collectLiveIndices();
        if (liveSize <= 0) return -1;

        ensureExactCapacity(liveSize);
        ensurePartitionHashCapacity(liveSize);
        int[] masks = liveModel.masks;
        char[][] chars = liveModel.words;
        long totalWeight = liveSize;
        if (totalWeight <= 0) return -1;
        precomputeExactOutcomeMasks(liveSize, chars);
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

            // Hash-map style accumulation of partition sizes keyed by reveal pattern bitmask.
            int partitionCount = 0;
            partHashEpoch++;
            if (partHashEpoch == Integer.MAX_VALUE) {
                Arrays.fill(partHashStamps, 0);
                partHashEpoch = 1;
            }
            int epoch = partHashEpoch;
            int hashMask = partHashKeys.length - 1;
            for (int i = 0; i < liveSize; i++) {
                int widx = exactLiveIdx[i];
                if ((masks[widx] & letterBit) == 0) continue;
                hitCount++;
                int key = exactOutcomeBuf[i * 26 + letterIdx];
                revealTotal += Integer.bitCount(key);
                int slot = mix32(key) & hashMask;
                while (partHashStamps[slot] == epoch && partHashKeys[slot] != key) {
                    slot = (slot + 1) & hashMask;
                }
                if (partHashStamps[slot] != epoch) {
                    partHashStamps[slot] = epoch;
                    partHashKeys[slot] = key;
                    partHashWeights[slot] = 0L;
                    partHashUsedSlots[partitionCount++] = slot;
                }
                partHashWeights[slot]++;
            }

            long missCount = totalWeight - hitCount;
            // Lower value means better expected split of remaining candidates after this guess.
            long expectedRemainNumerator = missCount * missCount;
            for (int p = 0; p < partitionCount; p++) {
                long count = partHashWeights[partHashUsedSlots[p]];
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
                            && lengthFreq[wordLenBucket][letterIdx] > lengthFreq[wordLenBucket][best])) {
                best = letterIdx;
                bestHitCount = hitCount;
                bestExpectedRemainNumerator = expectedRemainNumerator;
                bestRevealTotal = revealTotal;
            }

            bits &= bits - 1;
        }
        return best;
    }

    // Precomputes reveal-pattern masks used by exact partition scoring.
    private void precomputeExactOutcomeMasks(int liveSize, char[][] words)
    {
        // For each live word and letter, cache the revealed-position bitmask (e.g., 0b01001).
        Arrays.fill(exactOutcomeBuf, 0, liveSize * 26, 0);
        for (int i = 0; i < liveSize; i++) {
            int widx = exactLiveIdx[i];
            int base = i * 26;
            char[] word = words[widx];
            for (int pos = 0; pos < wordLen; pos++) {
                int letter = word[pos] - 'a';
                exactOutcomeBuf[base + letter] |= (1 << pos);
            }
        }
    }

    // Precomputes reveal potential for candidate tie-break letters.
    private void precomputeRevealScores(int unguessedMask)
    {
        Arrays.fill(revealCache, -1);
        int bits = unguessedMask;
        while (bits != 0) {
            int letterIdx = Integer.numberOfTrailingZeros(bits);
            int reveal = 0;
            // Sum how many live candidates would reveal this letter across all hidden slots.
            int posBits = unknownPosMask;
            while (posBits != 0) {
                int pos = Integer.numberOfTrailingZeros(posBits);
                reveal += intersectionCount(liveBits, liveModel.posBits[letterIdx][pos], liveModel.wordLongs);
                posBits &= posBits - 1;
            }
            revealCache[letterIdx] = reveal;
            bits &= bits - 1;
        }
    }

    // Syncs discovered letters from board text into bitmask constraints.
    private void syncFromCurrentWord(String currentWord)
    {
        int len = Math.min(wordLen, currentWord.length());
        for (int i = 0; i < len; i++) {
            char c = currentWord.charAt(i);
            if (c == ' ' || posPattern[i] == c) continue;
            posPattern[i] = c;
            presentMask |= LETTER_MASK[c - 'a'];
            unknownPosMask &= ~(1 << i);
            changedPos[changedPosCount++] = i;
        }
    }

    // Mixes an int key to spread hashes across the partition table.
    private static int mix32(int x)
    {
        x ^= (x >>> 16);
        x *= 0x7feb352d;
        x ^= (x >>> 15);
        x *= 0x846ca68b;
        x ^= (x >>> 16);
        return x;
    }

    // Builds a unique-letter bitmask for a word.
    private static int computeMask(char[] word)
    {
        int mask = 0;
        for (char c : word) mask |= LETTER_MASK[c - 'a'];
        return mask;
    }

    // Sets one bit in a packed long[] bitset.
    private static void setBit(long[] bits, int index)
    {
        bits[index >>> 6] |= (1L << (index & 63));
    }

    // In-place bitset intersection.
    private static void andWith(long[] dst, long[] src, int wordLongs)
    {
        for (int i = 0; i < wordLongs; i++) dst[i] &= src[i];
    }

    // In-place bitset subtraction.
    private static void andNotWith(long[] dst, long[] src, int wordLongs)
    {
        for (int i = 0; i < wordLongs; i++) dst[i] &= ~src[i];
    }

    // In-place bitset union.
    private static void orInto(long[] dst, long[] src, int wordLongs)
    {
        for (int i = 0; i < wordLongs; i++) dst[i] |= src[i];
    }

    // Counts set bits across a packed bitset.
    private static int popcount(long[] bits, int wordLongs)
    {
        int total = 0;
        for (int i = 0; i < wordLongs; i++) total += Long.bitCount(bits[i]);
        return total;
    }

    // Counts overlap size between two packed bitsets.
    private static int intersectionCount(long[] a, long[] b, int wordLongs)
    {
        int total = 0;
        for (int i = 0; i < wordLongs; i++) total += Long.bitCount(a[i] & b[i]);
        return total;
    }

    // Returns the index of the lone remaining candidate word.
    private int getSingleCandidateIndex()
    {
        for (int i = 0; i < liveModel.wordLongs; i++) {
            long v = liveBits[i];
            if (v == 0L) continue;
            return (i << 6) + Long.numberOfTrailingZeros(v);
        }
        return -1;
    }

    // Expands the live bitset into a dense index list for iteration.
    private int collectLiveIndices()
    {
        int write = 0;
        for (int i = 0; i < liveModel.wordLongs; i++) {
            long v = liveBits[i];
            while (v != 0L) {
                // Convert set bits in the packed bitset back into dense word indices.
                int bit = Long.numberOfTrailingZeros(v);
                exactLiveIdx[write++] = (i << 6) + bit;
                v &= v - 1;
            }
        }
        return write;
    }

    // Grows exact-scoring buffers when the live set outgrows capacity.
    private void ensureExactCapacity(int liveSize)
    {
        if (liveSize <= exactLiveIdx.length) return;
        // Grow both arrays together because exactOutcomeBuf is indexed by exactLiveIdx order.
        int cap = Math.max(liveSize + 8, exactLiveIdx.length << 1);
        exactLiveIdx = Arrays.copyOf(exactLiveIdx, cap);
        exactOutcomeBuf = Arrays.copyOf(exactOutcomeBuf, cap * 26);
    }

    // Grows hash-table arrays used to bucket exact reveal partitions.
    private void ensurePartitionHashCapacity(int liveSize)
    {
        int needed = liveSize << 1;
        int cap = partHashKeys.length;
        while (cap < needed) cap <<= 1;
        if (cap == partHashKeys.length) return;
        // Keep power-of-two capacity so mix32(key) & (cap - 1) stays valid and fast.
        partHashKeys = new int[cap];
        partHashWeights = new long[cap];
        partHashStamps = new int[cap];
        partHashUsedSlots = new int[cap];
        partHashEpoch = 1;
    }
}