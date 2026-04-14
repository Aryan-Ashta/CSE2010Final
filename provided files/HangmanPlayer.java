/*

  Authors (group members):
  Email addresses of group members:
  Group name:

  Course:
  Section:

  Description of the overall algorithm:


*/


public class HangmanPlayer
{

    // initialize HangmanPlayer with a file of English words
    public HangmanPlayer(String wordFile)
    {

    }

    // based on the current (partial or intitially blank) word
    //    guess a letter
    // currentWord: current word, currenWord.length has the length of the hidden word
    // isNewWord: indicates a new hidden word
    // returns the guessed letter
    // assume all letters are in lower case
    public char guess(String currentWord, boolean isNewWord)
    {
	char guess = ' ';
	
        return guess;
    }

    // feedback on the guessed letter
    // isCorrectGuess: true if the guessed letter is one of the letters in the hidden word
    // currentWord: partially filled or blank word
    //   
    // Case       isCorrectGuess      currentWord   
    // a.         true                partial word with the guessed letter
    //                                   or the whole word if the guessed letter was the
    //                                   last letter needed
    // b.         false               partial word without the guessed letter
    public void feedback(boolean isCorrectGuess, String currentWord)
    {

    }

}
