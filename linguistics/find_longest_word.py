def find_longest_word(filename):
    """Find the longest word in a file."""
    with open(filename, 'r') as file:
        words = file.read().split()
    
    longest = max(words, key=len)
    return longest

if __name__ == "__main__":
    result = find_longest_word('words.txt')
    print(f"The longest word is: {result}")