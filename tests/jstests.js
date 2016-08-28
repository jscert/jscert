% SERGIO: some of these rely on features we don't have yet, but it's useful to keep them around else I'll forget.

% APLAS 08

% automatic type conversion
var o={a:0}; o[{toString:function(){o.a++; return ”a”}}] % res: 1

% re-definable constructors, dynamic binding of literal creation (strictly ecma3 but fixed in most implementations
var a = {}; a % res: [object Object] 
Object = function(){return new Number()}; var b = {}; b % res: 0

% logical operators & type conversions
var a = true; if (a∗1) 1; else 0 % res: 1 
var b = {valueOf:function(){return 0}} 
var a = b&&b; if(a∗1) 1; else 0 % res: 0 
if (b) 1; else 0 % res: 1

% relational operators (rhino) & valueOf
x = 0; var a = {valueOf:function (){x=1}}; var b = {valueOf:function (){x=2}}; a<b; x % res: 2
% Yet, the evaluation order is not always left to right! 
x = 0; var a = {valueOf:function (){x=1}}; var b = {valueOf:function (){x=2}}; a>b; x % res: 1

% with and var
var n = {m:0}; with (n) {var m = 1}; n.m % res: 1 
m === undefined % res: true

% function and scope
(function (){var b=1; var c= function (){x=b}; c()})(); x % res: 1



% CSF 09

% scope and this
var getwin = function getscope(x){
if (x==0) {return this} else {getscope(0).ref=function(x){return x}; return getwin(0)}};
function a(){getwin(1).x=42};
a(); x % res: 42 

% type conversions
(f = function(){}, f.prototype = {a:12}, o = new f, o.toString = function(){return 30}, o[”a”] + o) % res: 42


% ESORICS 09

% fbjs vulnerability
($=e2,($ instanceof Object||$blacklist[$])?”bad”:$)
{toString:function(){this.toString=function(){return ”caller”}; return ”good”}}


% POPL 12

% scopes
x = null; y = null; z = null; f = function(w){x = v; v = 4; var v; y = v;}; v = 5; f(null); z = v; [x,y,z,v] % res: [undefined,4,5,5]

% with
a = {b:1}; with (a){f=function(c){return b}}; a = {b:2}; f(null) % res: 1


% @negative (I’m just adding this to avoid this test to be marked as “failed” where it should actually fail ☺ -- Martin)

