all:
	ocamlyacc ics/mss_parser.mly
	ocamllex ics/mss_lexer.mll
	ocamlyacc ics/tmss_parser.mly
	ocamllex ics/tmss_lexer.mll
	ocamlyacc ics/ics_parser.mly
	ocamllex ics/ics_lexer.mll
	ocamlfind ocamlc -g -o main -package oUnit -linkpkg -g \
	  -I ics ics/utils.ml \
	  ics/mss.ml ics/mss_parser.mli ics/mss_parser.ml ics/mss_lexer.ml \
	  ics/tmss.ml ics/tmss_parser.mli ics/tmss_parser.ml ics/tmss_lexer.ml \
	  ics/ics.ml ics/ics_parser.mli ics/ics_parser.ml ics/ics_lexer.ml \
	  ics/main.ml -I test \
		test/mss_parser_test.ml test/mss_test.ml \
		test/tmss_parser_test.ml test/tmss_test.ml \
		test/ics_parser_test.ml test/ics_test.ml \
		test/all_test.ml
	rm -rf ics/*.cm* ics/*_lexer.ml ics/*_parser.ml ics/*_parser.mli  test/*.cm* oUnit*
	./main
	rm -rf oUnit*
clean:
	rm -rf ics/*.cm* ics/*_lexer.ml ics/*_parser.ml ics/*_parser.mli  test/*.cm* oUnit* main

.PHONY: test all run

