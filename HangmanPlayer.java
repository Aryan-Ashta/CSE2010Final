
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
    private String[] allWords;      // all valid dictionary words, sorted by length
    private int[]    allMasks;      // allMasks[i] = letter-presence bitmask for allWords[i]
    private int[]    lengthStart;   // lengthStart[L] = first index in allWords for length L
    private int[]    lengthCount;   // lengthCount[L] = number of words of length L
 
    // Per-length letter frequency for out-of-vocabulary (OOV) fallback
    // fallbackFreq[L][c] = number of length-L words containing letter 'a'+c
    private int[][]  fallbackFreq;
 
    private static final int MAX_LEN = 64;
 
    // Per-hidden-word state (pre-allocated, never reallocated during guessing)
    private int[]    activeIdx;      // live candidates occupy activeIdx[0..activeCount-1]
    private int      activeCount;
    private boolean[] guessedLetters; // guessedLetters[i] = true if 'a'+i already guessed
    private int[]    liveFreq;       // live letter frequencies across active candidates
    private int      guessedMask;    // bitmask of letters already guessed
    private int      lastGuessIdx;   // index of most recent guess (0..25), or -1
    private int      absentMask;     // bitmask: bit i -> letter i confirmed absent
    private int      presentMask;    // bitmask: bit i -> letter i confirmed present
    private int      prevAbsentMask; // snapshot used for delta filtering
    private int      prevPresentMask;// snapshot used for delta filtering
    private char[]   posPattern;     // posPattern[i] = revealed char at position i, or ' '
    private char[]   prevPosPattern; // previous pattern snapshot for delta filtering
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
        allWords  = new String[total];
        allMasks  = new int[total];
        for (int i = 0; i < total; i++) {
            allWords[i] = tmp.get(i);
            allMasks[i] = computeMask(allWords[i]);
        }
        tmp = null; // allow GC
 
        // Build length index
        lengthStart = new int[MAX_LEN];
        lengthCount = new int[MAX_LEN];
        Arrays.fill(lengthStart, -1);
        for (int i = 0; i < total; i++) {
            int L = allWords[i].length();
            if (lengthStart[L] == -1) lengthStart[L] = i;
            lengthCount[L]++;
        }
 
        // Build per-length fallback frequencies
        fallbackFreq = new int[MAX_LEN][26];
        for (int i = 0; i < total; i++) {
            int L = allWords[i].length();
            int bits = allMasks[i];
            while (bits != 0) {
                int c = Integer.numberOfTrailingZeros(bits);
                fallbackFreq[L][c]++;
                bits &= bits - 1;
            }
        }
 
        // Pre-allocate activeIdx to the largest bucket size
        int maxBucket = 0;
        for (int L = 0; L < MAX_LEN; L++)
            if (lengthCount[L] > maxBucket) maxBucket = lengthCount[L];
        activeIdx      = new int[Math.max(maxBucket, 1)];
        guessedLetters = new boolean[26];
        liveFreq       = new int[26];
        posPattern     = new char[MAX_LEN];
        prevPosPattern = new char[MAX_LEN];
        Arrays.fill(prevPosPattern, ' ');
    }
 
 
    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            wordLen = currentWord.length();
            Arrays.fill(guessedLetters, false);
            guessedMask = 0;
            lastGuessIdx = -1;
            absentMask  = 0;
            presentMask = 0;
            prevAbsentMask = 0;
            prevPresentMask = 0;
            Arrays.fill(prevPosPattern, ' ');
 
            for (int i = 0; i < wordLen; i++)
                posPattern[i] = currentWord.charAt(i); // all ' ' at start
 
            // Load length bucket into activeIdx
            if (wordLen < MAX_LEN && lengthStart[wordLen] != -1) {
                activeCount = lengthCount[wordLen];
                int start   = lengthStart[wordLen];
                for (int i = 0; i < activeCount; i++)
                    activeIdx[i] = start + i;
            } else {
                activeCount = 0;
            }

            // Build starting live frequencies once for this word
            rebuildLiveFreq();
        }
 
        // Sync posPattern and presentMask with currentWord (in case called before feedback)
        for (int i = 0; i < wordLen; i++) {
            char c = currentWord.charAt(i);
            if (c != ' ') {
                posPattern[i] = c;
                presentMask |= (1 << (c - 'a'));
            }
        }
 
        // Apply only constraints that are new since the last snapshot
        filterCandidatesByDelta();
 
        // Pick best unguessed letter by live active-candidate frequency
        int best = -1;
        for (int i = 0; i < 26; i++) {
            if (!guessedLetters[i] && liveFreq[i] > 0)
                if (best == -1 || liveFreq[i] > liveFreq[best]) best = i;
        }
 
        // Fallback: per-length precomputed frequency (handles OOV words)
        if (best == -1) {
            int L = Math.min(wordLen, MAX_LEN - 1);
            for (int i = 0; i < 26; i++) {
                if (!guessedLetters[i])
                    if (best == -1 || fallbackFreq[L][i] > fallbackFreq[L][best]) best = i;
            }
        }
 
        // Last resort: English letter frequency order
        if (best == -1) {
            for (char c : FREQ_ORDER) {
                int idx = c - 'a';
                if (!guessedLetters[idx]) { best = idx; break; }
            }
        }
 
        guessedLetters[best] = true;
        guessedMask |= (1 << best);
        lastGuessIdx = best;
        return (char)('a' + best);
    }
 
 
    public void feedback(boolean isCorrectGuess, String currentWord)
    {
        if (!isCorrectGuess) {
            // The letter guessed but not revealed anywhere is confirmed absent
            if (lastGuessIdx >= 0 && ((presentMask >> lastGuessIdx & 1) == 0))
                absentMask |= (1 << lastGuessIdx);
        } else {
            // Update posPattern and presentMask with newly revealed positions
            for (int i = 0; i < wordLen && i < currentWord.length(); i++) {
                char c = currentWord.charAt(i);
                if (c != ' ') {
                    posPattern[i] = c;
                    presentMask |= (1 << (c - 'a'));
                }
            }
        }

        // Keep candidate set/live frequencies current for the next guess turn.
        filterCandidatesByDelta();
    }
 
 
    private void filterCandidatesByDelta()
    {
        int newAbsentBits = absentMask & ~prevAbsentMask;
        int newPresentBits = presentMask & ~prevPresentMask;
        boolean hasNewReveals = false;
        for (int i = 0; i < wordLen; i++) {
            if (prevPosPattern[i] != posPattern[i]) {
                hasNewReveals = true;
                break;
            }
        }

        // Nothing new since last filtering pass.
        if (newAbsentBits == 0 && newPresentBits == 0 && !hasNewReveals) return;

        int write = 0;
        for (int read = 0; read < activeCount; read++) {
            int widx = activeIdx[read];
            int mask = allMasks[widx];
 
            // Fast delta checks using only new constraints.
            if ((mask & newAbsentBits) != 0) {
                removeFromLiveFreq(widx);
                continue;
            }
            if ((mask & newPresentBits) != newPresentBits) {
                removeFromLiveFreq(widx);
                continue;
            }
 
            // Check only newly revealed position constraints.
            if (!positionMatchDelta(allWords[widx])) {
                removeFromLiveFreq(widx);
                continue;
            }
 
            activeIdx[write++] = widx;
        }
        activeCount = write;
        snapshotFilterState();
    }
 
    private boolean positionMatchDelta(String word)
    {
        for (int i = 0; i < wordLen; i++) {
            char p = posPattern[i];
            if (p == prevPosPattern[i]) continue; // unchanged since last snapshot
            if (p != ' ' && word.charAt(i) != p) return false;
        }
        return true;
    }

    private void snapshotFilterState()
    {
        prevAbsentMask = absentMask;
        prevPresentMask = presentMask;
        for (int i = 0; i < wordLen; i++) prevPosPattern[i] = posPattern[i];
    }

    private void rebuildLiveFreq()
    {
        Arrays.fill(liveFreq, 0);
        int unguessedAll = ~guessedMask;
        for (int i = 0; i < activeCount; i++) {
            int bits = allMasks[activeIdx[i]] & unguessedAll;
            while (bits != 0) {
                int c = Integer.numberOfTrailingZeros(bits);
                liveFreq[c]++;
                bits &= bits - 1;
            }
        }
    }

    private void removeFromLiveFreq(int widx)
    {
        int bits = allMasks[widx] & ~guessedMask;
        while (bits != 0) {
            int c = Integer.numberOfTrailingZeros(bits);
            liveFreq[c]--;
            bits &= bits - 1;
        }
    }
 
 
    // Helpers
    private static int computeMask(String word)
    {
        int mask = 0;
        for (int i = 0; i < word.length(); i++)
            mask |= (1 << (word.charAt(i) - 'a'));
        return mask;
    }
}