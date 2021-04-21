(lang dune 2.5)
(name lambda-amor)
(version 0.1)
(generate_opam_files true)
(authors "Joseph W. Cutler")

(package
 (name lambda-amor)
 (synopsis "An implementation of Rajani et al's Lambda-Amor")
 (description "")
 (depends why3 core (odoc :with-doc)))