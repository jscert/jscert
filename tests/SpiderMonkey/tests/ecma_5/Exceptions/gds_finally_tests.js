assertEq('try',
         eval(
          "try{ \
            'try'\
          } finally {\
            'finally' \
          }"),
         "try-finally block should return try value, not finally value");

assertEq('try',
         eval(
             "while(true) {\
                 try{ \
                     'try';\
                     break \
                 } finally { \
                     'finally' \
                 }\
             }"),
         "try-finally block should return try value, not finally value");

assertEq('try',
         eval(
             "x = 'loop';\
             while(x=='loop') { \
                 x = 'stop looping' ;\
                 try{ \
                     'try' ;\
                     break \
                 } finally { \
                     'finally' \
                 } ; \
                 x = 'done' \
             }"),
         "try-finally block should return try value, not finally value");
assertEq('stop looping',
         eval(
             "x = 'loop' ;\
             while(x=='loop') { \
                 x = 'stop looping' ;\
                 try{\
                     'try' ;\
                     break\
                 } finally { \
                     'finally' \
                 } ; \
                     x = 'done' \
                 } ; \
                 x"),
         "try-finally block should return try value, not finally value");

assertEq('finally',
         eval(
             "while(true) { \
                 try{\
                     'try'\
                 } finally {\
                     'finally'; \
                     break\
                 } \
             }"),
         "try-finally block should return finally value if it has non-normal completion type");
assertEq('',
         eval(
             "while(true) { \
                 try{\
                     'try'\
                 } finally {\
                     break\
                 }\
             }"),
         "try-finally block should return finally value if it has a non-normal completion type");

assertEq('try',
         eval(
             "x = 'loop' ;\
             while(x=='loop') {\
                 x = 'stop looping' ;\
                 try{\
                     'try' ;\
                     break\
                 } finally { } ;\
                 x = 'done'\
             }"),
         "try-finally block should return try value, not finally value");

assertEq('try',
         eval(
             "x = 'loop' ;\
             while(x=='loop') {\
                 x = 'stop looping' ;\
                 try{\
                     'try' ;\
                     break\
                 } finally { \
                     if(4){} \
                 } ; \
                 x = 'done'\
             }"),
         "try-finally block should return try value, not finally value");

assertEq('catch',
         eval(
             "try{\
                 throw 'exception'\
             } catch(e) { \
                 'catch'\
             } finally { \
                 'finally'\
             }"),
         "try-catch-finally block should return catch value, not finally value");

assertEq('catch',
         eval(
             "while(true) {\
                 try{\
                     throw 'exception'\
                 }catch(e){ \
                     'catch' ; \
                     break \
                 } finally { \
                     'finally' \
                 } \
             }"),
         "try-catch-finally block should return catch value, not finally value");

assertEq('catch',
         eval(
             "x = 'loop' ;\
             while(x=='loop') { \
                 x = 'stop looping' ;\
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch' ;\
                     break\
                 } finally { \
                     'finally' \
                 } ; \
                 x = 'done' \
             }"),
         "try-catch-finally block should return catch value, not finally value");

assertEq('stop looping',
         eval(
             "x = 'loop' ;\
             while(x=='loop') { \
                 x = 'stop looping' ;\
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch' ; \
                     break\
                 } finally { \
                     'finally' \
                 } ; \
                 x = 'done'\
             } ;\
             x"),
         "try-catch-finally block should return catch value, not finally value");

assertEq('finally',
         eval(
             "while(true) { \
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch'\
                 } finally {\
                     'finally';\
                     break\
                 } \
             }"),
         "try-catch-finally block should the finally value if it has a non-normal completion type");
assertEq('',
         eval(
             "while(true) {\
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch'\
                 } finally {\
                     break\
                 } \
             }"),
         "try-catch-finally block should the finally value if it has a non-normal completion type");

assertEq('catch',
         eval(
             "x = 'loop' ;\
             while(x=='loop') { \
                 x = 'stop looping' ; \
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch' ; \
                     break\
                 } finally { } ; \
                 x = 'done' \
             }"),
         "try-catch-finally block should return catch value, not finally value");

assertEq('catch',
         eval(
             "x = 'loop' ; \
             while(x=='loop') { \
                 x = 'stop looping' ;\
                 try{\
                     throw 'exception'\
                 }catch(e){\
                     'catch' ;\
                     break\
                 } finally {\
                     if(4){} \
                 } ; \
                 x = 'done'\
             }"),
         "try-catch-finally block should return catch value, not finally value");
