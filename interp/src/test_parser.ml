open OUnit
open Interpreter

let test_small () =
  let prog1 = 
    "x = 5" in
  let exp = Translate_syntax.coq_syntax_from_string prog1 in
  assert_equal 
    (Prog_stat (Stat_expr ((Expr_assign (Expr_variable ['x'], None, Expr_literal (Literal_number 5.0))))))
    exp
    
let test_interpreter_small () =
  let prog1 = 
    "x = 5" in
  let exp = Translate_syntax.coq_syntax_from_string prog1 in
  let res = run_prog max_int init_heap init_scope exp in
  assert_equal 
    true 
    (match res with Out_return (_, Ret_ret_expr (Ret_expr_value (Value_number 5.0))) -> true | _ -> false)
    
let test_prog1 () =
  let prog1 = 
	"{convert = function(n) { return n (function(n) { return n + 1 }) (0) };

	succ = function(n) { return function(f) { return function(x) {
		return n (f) (f (x))
	  }}};

	zero = function(f) { return function(x) { return x } };

	plus = function(x) { return function(y) { return x (succ) (y) }};

	times = function(x) { return function(y) { return x (plus (y)) (zero) }};

	exp = function(x) { return function(y) { return y (x) }};

	var one = succ (zero);
	var two = plus (one) (one);
	var three = plus (two) (one);

	var six = times (three) (two);

	convert (exp (two) (six))}" in
  let exp = Translate_syntax.coq_syntax_from_string prog1 in
  assert_equal (Prog_stat Interpreter.prog1) exp

let test_prog2 () =
  let prog2 = 
    "{ var id = function(x) { return x }; /* To deference the final value. */

			 var f = function() {
			   this.x = 0;
			   this.g = function() { this.x = 1; return this };
			   void 42 
			 };
			
			 var h = function() { void 42 };
			 h.prototype = new f();
			
			 var test = new h();
			
			 id(test.g().x) }" in
  let exp = Translate_syntax.coq_syntax_from_string prog2 in
  assert_equal (Prog_stat Interpreter.prog2) exp
  
let test_prog3 () =
  let prog3 = 
    "{ var x = 24;
       var f = function (){ return x; };
       f() }" in
  let exp = Translate_syntax.coq_syntax_from_string prog3 in
  assert_equal (Prog_stat Interpreter.prog3) exp

  
let suite = "Testing Parser" >:::
  ["test small" >:: test_small;
   "test interpreter small" >:: test_interpreter_small;
   "test prog1" >:: test_prog1;
   "test prog2" >:: test_prog2;
   "test_prog3" >:: test_prog3
  ]
  
  let arguments () =
    let usage_msg="Usage: -jsparser <path>" in
    Arg.parse
      ["-jsparser", Arg.String(fun f -> Parser_main.js_to_xml_parser := f), "path to js_parser.jar"]
      (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
      usage_msg
  
  let _ = 
    arguments (); 
    run_test_tt_main suite
