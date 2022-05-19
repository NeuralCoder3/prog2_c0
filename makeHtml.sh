eval $(opam env)
# alectryon -R . Lib -I . --frontend coq proofs.v
alectryon -R . Lib -I . --frontend coq --backend webpage proofs.v -o html/proofs.html