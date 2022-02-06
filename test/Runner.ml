let () =
  Alcotest.run "LFind"
    (
      [ "Test Setup", Test_Setup.all;
        "Test Examples", Test_Examples.all;
        "Test Generalization", Test_Generalization.all;
      ]
    )
