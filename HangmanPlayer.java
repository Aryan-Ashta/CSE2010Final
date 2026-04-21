
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
    // Preprocessed dictionary (flat arrays grouped by word length)
    private char[][] wordChars;     // all valid dictionary words as char arrays, sorted by length
    private int[]    allMasks;      // allMasks[i] = letter-presence bitmask for allWords[i]
    private int[]    lengthStart;   // lengthStart[L] = first index in allWords for length L
    private int[]    lengthCount;   // lengthCount[L] = number of words of length L
 
    // Per-length letter frequency for out-of-vocabulary (OOV) fallback
    // lengthFreq[L][c] = number of length-L words containing letter 'a'+c
    private int[][]  lengthFreq;
 
    private static final int MAX_LEN = 24;
    private static final int[] LETTER_MASK = new int[26];
    private static final int ALL_LETTERS_MASK = (1 << 26) - 1;
    static {
        for (int i = 0; i < 26; i++) LETTER_MASK[i] = 1 << i;
    }
 
    // Per-hidden-word state (pre-allocated, never reallocated during guessing)
    private int[]    activeIdx;      // live candidates occupy activeIdx[0..activeCount-1]
    private int      activeCount;
    private int[]    liveFreq;       // live letter frequencies across active candidates
    private int      guessedMask;    // bitmask of letters already guessed
    private int      lastGuessIdx;   // index of most recent guess (0..25), or -1
    private int      absentMask;     // bitmask: bit i -> letter i confirmed absent
    private int      presentMask;    // bitmask: bit i -> letter i confirmed present
    private int      prevAbsentMask; // snapshot used for delta filtering
    private int      prevPresentMask;// snapshot used for delta filtering
    private char[]   posPattern;     // posPattern[i] = revealed char at position i, or ' '
    private int[]    changedPos;     // positions newly revealed since last filter pass
    private int      changedPosCount;
    private int      wordLen;
 
    // English letter frequency fallback (last resort)
    private static final char[] FREQ_ORDER =
        "etaoinshrdlcumwfgypbvkjxqz".toCharArray();
 
 
    // Constructor
    public HangmanPlayer(String wordFile)
    {
        // Pass 1: read all valid alphabetic words
        ArrayList<String> tmp = new ArrayList<>();
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
                if (ok) tmp.add(w);
            }
        }
        catch (IOException e) {
            System.err.println("Error reading word file: " + e.getMessage());
        }
 
        // Sort by length to enable flat-array bucketing
        tmp.sort(Comparator.comparingInt(String::length));
 
        // Build flat arrays
        int total = tmp.size();
        wordChars = new char[total][];
        allMasks  = new int[total];
        for (int i = 0; i < total; i++) {
            char[] chars = tmp.get(i).toCharArray();
            wordChars[i] = chars;
            allMasks[i]  = computeMask(chars);
        }
        tmp = null; // allow GC
 
        // Build length index
        lengthStart = new int[MAX_LEN];
        lengthCount = new int[MAX_LEN];
        Arrays.fill(lengthStart, -1);
        for (int i = 0; i < total; i++) {
            int L = wordChars[i].length;
            if (lengthStart[L] == -1) lengthStart[L] = i;
            lengthCount[L]++;
        }
 
        // Build per-length frequencies
        lengthFreq = new int[MAX_LEN][26];
        for (int i = 0; i < total; i++) {
            int L = wordChars[i].length;
            int bits = allMasks[i];
            while (bits != 0) {
                int c = Integer.numberOfTrailingZeros(bits);
                lengthFreq[L][c]++;
                bits &= bits - 1;
            }
        }
 
        // Pre-allocate activeIdx to the largest bucket size
        int maxBucket = 0;
        for (int L = 0; L < MAX_LEN; L++)
            if (lengthCount[L] > maxBucket) maxBucket = lengthCount[L];
        activeIdx      = new int[Math.max(maxBucket, 1)];
        liveFreq       = new int[26];
        posPattern     = new char[MAX_LEN];
        changedPos     = new int[MAX_LEN];
    }
 
 
    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            wordLen = currentWord.length();
            guessedMask = 0;
            lastGuessIdx = -1;
            absentMask  = 0;
            presentMask = 0;
            prevAbsentMask = 0;
            prevPresentMask = 0;
            changedPosCount = 0;
            Arrays.fill(posPattern, 0, wordLen, ' ');
 
            // Load length bucket into activeIdx
            if (wordLen < MAX_LEN && lengthStart[wordLen] != -1) {
                activeCount = lengthCount[wordLen];
                int start   = lengthStart[wordLen];
                for (int i = 0; i < activeCount; i++)
                    activeIdx[i] = start + i;
            } else {
                activeCount = 0;
            }

            // Initialize live frequencies from precomputed per-length table.
            if (wordLen < MAX_LEN) {
                System.arraycopy(lengthFreq[wordLen], 0, liveFreq, 0, 26);
            } else {
                Arrays.fill(liveFreq, 0);
            }
        }
 
        // Sync posPattern/presentMask and changed positions with currentWord.
        syncFromCurrentWord(currentWord);
 
        // Apply only constraints that are new since the last snapshot
        filterCandidatesByDelta();
 
        // Pick best unguessed letter by live active-candidate frequency
        int[] freq = liveFreq;
        int unguessedMask = ALL_LETTERS_MASK & ~guessedMask;
        int bits = unguessedMask;
        int best = -1;
        int bestFreq = 0;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            int f = freq[i];
            if (f > bestFreq) {
                bestFreq = f;
                best = i;
            }
            bits &= bits - 1;
        }
 
        // Fallback: per-length precomputed frequency (handles OOV words)
        if (best == -1) {
            int L = Math.min(wordLen, MAX_LEN - 1);
            int[] fallback = lengthFreq[L];
            bits = unguessedMask;
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
        int newAbsentBits = absentMask & ~prevAbsentMask;
        int newPresentBits = presentMask & ~prevPresentMask;
        int changedCount = changedPosCount;
        int[] changed = changedPos;
        char[] currPattern = posPattern;

        // Nothing new since last filtering pass.
        if (newAbsentBits == 0 && newPresentBits == 0 && changedCount == 0) return;

        int[] active = activeIdx;
        int[] masks = allMasks;
        char[][] chars = wordChars;
        int[] freq = liveFreq;
        int unguessed = ALL_LETTERS_MASK & ~guessedMask;
        int write = 0;
        for (int read = 0; read < activeCount; read++) {
            int widx = active[read];
            int mask = masks[widx];
            boolean keep = true;
 
            // Fast delta checks using only new constraints.
            if ((mask & newAbsentBits) != 0) {
                keep = false;
            }
            if (keep && (mask & newPresentBits) != newPresentBits) {
                keep = false;
            }
 
            // Check only newly revealed position constraints (inlined hot-path logic).
            if (keep && changedCount != 0) {
                char[] word = chars[widx];
                for (int i = 0; i < changedCount; i++) {
                    int pos = changed[i];
                    if (word[pos] != currPattern[pos]) {
                        keep = false;
                        break;
                    }
                }
            }

            if (!keep) {
                int bits = mask & unguessed;
                while (bits != 0) {
                    int c = Integer.numberOfTrailingZeros(bits);
                    freq[c]--;
                    bits &= bits - 1;
                }
                continue;
            }
 
            active[write++] = widx;
        }
        activeCount = write;
        snapshotFilterState();
    }

    private void snapshotFilterState()
    {
        prevAbsentMask = absentMask;
        prevPresentMask = presentMask;
        changedPosCount = 0;
    }
 
 
    // Helpers
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
}