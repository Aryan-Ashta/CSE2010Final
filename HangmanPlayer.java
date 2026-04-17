
/*

  Authors (group members): Aryan Ashta
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
    private int      absentMask;     // bitmask: bit i -> letter i confirmed absent
    private int      presentMask;    // bitmask: bit i -> letter i confirmed present
    private char[]   posPattern;     // posPattern[i] = revealed char at position i, or ' '
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
        posPattern     = new char[MAX_LEN];
    }
 
 
    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            wordLen = currentWord.length();
            Arrays.fill(guessedLetters, false);
            absentMask  = 0;
            presentMask = 0;
 
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
        }
 
        // Sync posPattern and presentMask with currentWord (in case called before feedback)
        for (int i = 0; i < wordLen; i++) {
            char c = currentWord.charAt(i);
            if (c != ' ') {
                posPattern[i] = c;
                presentMask |= (1 << (c - 'a'));
            }
        }
 
        // Filter candidates
        filterCandidates();
 
        // Count letter frequencies with bit tricks
        int[] freq       = new int[26];
        int guessedMask  = buildGuessedMask();
        int unguessedAll = ~guessedMask;
 
        for (int ci = 0; ci < activeCount; ci++) {
            int bits = allMasks[activeIdx[ci]] & unguessedAll;
            while (bits != 0) {
                int c = Integer.numberOfTrailingZeros(bits);
                freq[c]++;
                bits &= bits - 1;
            }
        }
 
        // Pick best unguessed letter by frequency
        int best = -1;
        for (int i = 0; i < 26; i++) {
            if (!guessedLetters[i] && freq[i] > 0)
                if (best == -1 || freq[i] > freq[best]) best = i;
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
        return (char)('a' + best);
    }
 
 
    public void feedback(boolean isCorrectGuess, String currentWord)
    {
        if (!isCorrectGuess) {
            // The letter guessed but not revealed anywhere is confirmed absent
            for (int i = 0; i < 26; i++) {
                if (guessedLetters[i] && ((presentMask >> i & 1) == 0))
                    absentMask |= (1 << i);
            }
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
    }
 
 
    private void filterCandidates()
    {
        int write = 0;
        for (int read = 0; read < activeCount; read++) {
            int widx = activeIdx[read];
            int mask = allMasks[widx];
 
            // Level 1: bitmask checks (O(1))
            if ((mask & absentMask)  != 0)          continue; // contains absent letter
            if ((mask & presentMask) != presentMask) continue; // missing required letter
 
            // Level 2: position match (O(L))
            if (!positionMatch(allWords[widx]))      continue;
 
            activeIdx[write++] = widx;
        }
        activeCount = write;
    }
 
    private boolean positionMatch(String word)
    {
        for (int i = 0; i < wordLen; i++) {
            char p = posPattern[i];
            if (p != ' ') {
                // Revealed position: candidate must match exactly
                if (word.charAt(i) != p) return false;
            } else {
                
                //fix here
                int idx = word.charAt(i) - 'a';
                if (idx >= 0 && idx < 26 && (presentMask >> idx & 1) == 1) return false;
            }
        }
        return true;
    }
 
 
    // Helpers
    private static int computeMask(String word)
    {
        int mask = 0;
        for (int i = 0; i < word.length(); i++)
            mask |= (1 << (word.charAt(i) - 'a'));
        return mask;
    }
 
    private int buildGuessedMask()
    {
        int mask = 0;
        for (int i = 0; i < 26; i++)
            if (guessedLetters[i]) mask |= (1 << i);
        return mask;
    }
}