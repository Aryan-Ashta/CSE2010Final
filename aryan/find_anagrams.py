from collections import defaultdict

def find_anagrams(file_path):
    groups = defaultdict(dict)

    # Read file
    with open(file_path, "r", encoding="utf-8") as f:
        for line in f:
            word = line.strip()
            if not word:
                continue

            # Group anagrams case-insensitively.
            key = "".join(sorted(word.lower()))
            # Treat words that differ only by case as duplicates.
            groups[key].setdefault(word.lower(), word)

    # Filter only real anagram groups
    return {k: list(v.values()) for k, v in groups.items() if len(v) > 1}


if __name__ == "__main__":
    file_path = "provided files/words.txt"
    output_path = "aryan/linguistics/anagrams.txt"
    anagrams = find_anagrams(file_path)

    with open(output_path, "w", encoding="utf-8") as out:
        for group in anagrams.values():
            line = ", ".join(group)
            print(line)
            out.write(line + "\n")