import random

# Read all words from file
with open("words.txt", "r", encoding="utf-8") as f:
    words = [line.strip() for line in f if line.strip()]

# Ensure there are enough words
if len(words) < 1000:
    raise ValueError("words.txt must contain at least 1000 words.")

# Generate hiddenWords2 through hiddenWords100
for i in range(2, 101):
    sample = random.sample(words, 1000)
    filename = f"hiddenWords{i}.txt"
    
    with open(filename, "w", encoding="utf-8") as out:
        out.write("\n".join(sample))

print("Files generated: hiddenWords2.txt through hiddenWords100.txt")