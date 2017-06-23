# Rename all *.txt to *.text
for f in *.s; do 
mv -- "$f" "${f%}.s1"
done
