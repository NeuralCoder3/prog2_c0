eval $(opam env)

rm -f html/*.*

# alectryon -R . Lib -I . --frontend coq proofs.v
alectryon -R . Lib -I . --frontend coq --backend webpage proofs.v -o html/proofs.html

rm -f neuralcoder3.github.io/proofs/while/*.*
cp html/* neuralcoder3.github.io/proofs/while/

cd neuralcoder3.github.io
git add proofs
git commit -m "update"
git push