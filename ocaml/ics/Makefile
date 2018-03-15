all:
	ocamlyacc mss/mss_parser.mly
	ocamllex mss/mss_lexer.mll
	ocamlyacc mss/tmss_parser.mly
	ocamllex mss/tmss_lexer.mll
	ocamlyacc mss/ics_parser.mly
	ocamllex mss/ics_lexer.mll
	ocamlfind ocamlc -g -o main -package oUnit -linkpkg -g \
	  -I mss mss/utils.ml \
	  mss/mss.ml mss/mss_parser.mli mss/mss_parser.ml mss/mss_lexer.ml \
	  mss/tmss.ml mss/tmss_parser.mli mss/tmss_parser.ml mss/tmss_lexer.ml \
	  mss/ics.ml mss/ics_parser.mli mss/ics_parser.ml mss/ics_lexer.ml \
	  mss/main.ml -I test \
		test/mss_parser_test.ml test/mss_test.ml \
		test/tmss_parser_test.ml test/tmss_test.ml \
		test/ics_parser_test.ml test/ics_test.ml \
		test/all_test.ml
	rm -rf mss/*.cm* mss/*_lexer.ml mss/*_parser.ml mss/*_parser.mli  test/*.cm* oUnit*
	./main
	rm -rf oUnit*
clean:
	rm -rf mss/*.cm* mss/*_lexer.ml mss/*_parser.ml mss/*_parser.mli  test/*.cm* oUnit* main

.PHONY: test all run

