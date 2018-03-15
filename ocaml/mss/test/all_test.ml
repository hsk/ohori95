open OUnit

let _ =
  run_test_tt_main("All test" >::: [
    Mss_parser_test.test();
    Mss_test.eval();
    Mss_test.esub();
    Tmss_parser_test.parseq1();
    Tmss_parser_test.parsek();
    Tmss_parser_test.parseq2();
    Tmss_parser_test.parseM();
    Tmss_test.test_eftv();
    Tmss_test.test_cls();
    Tmss_test.test_typing();
    Ics_parser_test.test_parseC();
    Ics_test.test_csub();
    Ics_test.test_eval();
    Ics_test.test_kinding();
    Ics_test.test_index_judgment();
    Ics_test.test_rep();
    Ics_test.test_compile();
  ])
