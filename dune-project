(lang dune 3.16)

(using mdx 0.4)

(generate_opam_files true)

(name hope-2024)

(source
 (github patricoferris/hope-2024))

(license ISC)

(authors "Patrick Ferris")

(maintainers "patrick@sirref.org")

(package
  (allow_empty)
  (synopsis "Code for HOPE 2024")
  (description "")
  (name hope-2024)
  (depends
    (fstar (= "dev"))
    (mdx (and :with-test (= "dev")))))
