eval $(opam env)

rm -f html/*.*

# alectryon -R . Lib -I . --frontend coq proofs.v
# alectryon -R . Lib -I . --frontend coq --backend webpage proofs.v -o html/proofs.html
alectryon -R . Prog2Hoare -I . --frontend coq --backend webpage *.v
mv *.html html/
mv *.js html/
mv *.css html/

rm -f neuralcoder3.github.io/proofs/while/hoare/*.*
cp html/* neuralcoder3.github.io/proofs/while/hoare/

cd neuralcoder3.github.io
git add proofs
git commit -m "update"
git push