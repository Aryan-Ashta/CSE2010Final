package aryan;

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
    private HashMap<Integer, ArrayList<String>> wordsByLength;

    private ArrayList<String> candidates;
    private boolean[] guessedLetters;

    private static final char[] FREQ_ORDER =
        "etaoinshrdlcumwfgypbvkjxqz".toCharArray();


    public HangmanPlayer(String wordFile)
    {
        wordsByLength = new HashMap<>();

        try (BufferedReader br = new BufferedReader(
                new InputStreamReader(new FileInputStream(wordFile), "UTF-8")))
        {
            String line;
            while ((line = br.readLine()) != null)
            {
                String word = line.trim().toLowerCase();
                if (word.isEmpty()) continue;

                boolean valid = true;
                for (int i = 0; i < word.length(); i++) {
                    char c = word.charAt(i);
                    if (c < 'a' || c > 'z') { valid = false; break; }
                }
                if (!valid) continue;

                int len = word.length();
                ArrayList<String> bucket = wordsByLength.get(len);
                if (bucket == null) {
                    bucket = new ArrayList<>();
                    wordsByLength.put(len, bucket);
                }
                bucket.add(word);
            }
        }
        catch (IOException e)
        {
            System.err.println("Error reading word file: " + e.getMessage());
        }
    }


    public char guess(String currentWord, boolean isNewWord)
    {
        if (isNewWord)
        {
            guessedLetters = new boolean[26];

            int len = currentWord.length();
            ArrayList<String> pool = wordsByLength.get(len);

            candidates = (pool != null)
                ? new ArrayList<>(pool)
                : new ArrayList<>();
        }

        filterCandidates(currentWord);

        int[] freq = new int[26];
        for (int ci = 0; ci < candidates.size(); ci++)
        {
            String word = candidates.get(ci);
            boolean[] counted = new boolean[26];
            for (int i = 0; i < word.length(); i++)
            {
                int idx = word.charAt(i) - 'a';
                if (!guessedLetters[idx] && !counted[idx])
                {
                    freq[idx]++;
                    counted[idx] = true;
                }
            }
        }

        int best = -1;
        for (int i = 0; i < 26; i++)
        {
            if (!guessedLetters[i] && freq[i] > 0)
            {
                if (best == -1 || freq[i] > freq[best])
                    best = i;
            }
        }

        if (best == -1)
        {
            for (char c : FREQ_ORDER)
            {
                int idx = c - 'a';
                if (!guessedLetters[idx])
                {
                    best = idx;
                    break;
                }
            }
        }

        guessedLetters[best] = true;
        return (char) ('a' + best);
    }


    public void feedback(boolean isCorrectGuess, String currentWord)
    {
    }


    private void filterCandidates(String currentWord)
    {
        boolean[] confirmedInWord  = new boolean[26];
        boolean[] confirmedAbsent  = new boolean[26];

        for (int i = 0; i < currentWord.length(); i++)
        {
            char c = currentWord.charAt(i);
            if (c != ' ')
                confirmedInWord[c - 'a'] = true;
        }

        for (int i = 0; i < 26; i++)
        {
            if (guessedLetters[i] && !confirmedInWord[i])
                confirmedAbsent[i] = true;
        }

        Iterator<String> it = candidates.iterator();
        while (it.hasNext())
        {
            if (!matches(it.next(), currentWord, confirmedAbsent, confirmedInWord))
                it.remove();
        }
    }


    private boolean matches(String word, String pattern,
                             boolean[] confirmedAbsent, boolean[] confirmedInWord)
    {
        int len = pattern.length();
        if (word.length() != len) return false;

        for (int i = 0; i < len; i++)
        {
            char wc  = word.charAt(i);
            char pc  = pattern.charAt(i);
            int  idx = wc - 'a';

            if (pc == ' ')
            {
                if (confirmedAbsent[idx]) return false;
            }
            else
            {
                if (wc != pc) return false;
            }
        }

        for (int i = 0; i < 26; i++)
        {
            if (confirmedInWord[i])
            {
                boolean found = false;
                for (int j = 0; j < len; j++)
                {
                    if (word.charAt(j) - 'a' == i) { found = true; break; }
                }
                if (!found) return false;
            }
        }

        return true;
    }
}