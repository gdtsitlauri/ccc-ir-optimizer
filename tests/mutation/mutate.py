"""mutate.py SRC MUTANTS NAME OUT - writes SRC with mutant NAME applied to OUT."""
import sys

src, mutants, name, out = sys.argv[1:5]
for line in open(mutants).read().splitlines():
    parts = line.split('@@')
    if line.startswith('#') or parts[0] != name:
        continue
    _, old, new = parts
    text = open(src, newline='').read()
    if text.count(old) != 1:
        sys.exit(f'{name}: the original text occurs {text.count(old)} times in {src}')
    open(out, 'w', newline='').write(text.replace(old, new))
    break
else:
    sys.exit(f'no mutant named {name}')
