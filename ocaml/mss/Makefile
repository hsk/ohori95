all:
	ocamlyacc src/mss_parser.mly
	ocamllex src/mss_lexer.mll
	ocamlyacc src/tmss_parser.mly
	ocamllex src/tmss_lexer.mll
	ocamlyacc src/ics_parser.mly
	ocamllex src/ics_lexer.mll
	ocamlfind ocamlc -g -o main -package oUnit -linkpkg -g \
	  -I src src/utils.ml \
	  src/mss.ml src/mss_parser.mli src/mss_parser.ml src/mss_lexer.ml \
	  src/tmss.ml src/tmss_parser.mli src/tmss_parser.ml src/tmss_lexer.ml \
	  src/ics.ml src/ics_parser.mli src/ics_parser.ml src/ics_lexer.ml \
	  src/main.ml -I test \
		test/mss_parser_test.ml test/mss_test.ml \
		test/tmss_parser_test.ml test/tmss_test.ml \
		test/ics_parser_test.ml test/ics_test.ml \
		test/all_test.ml
	rm -rf src/*.cm* src/*_lexer.ml src/*_parser.ml src/*_parser.mli  test/*.cm* oUnit*
	./main
	rm -rf oUnit*
clean:
	rm -rf src/*.cm* src/*_lexer.ml src/*_parser.ml src/*_parser.mli  test/*.cm* oUnit* main

.PHONY: test all run

