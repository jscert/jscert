TLC=tlc
FLOCQ=flocq
COQBIN=
if [ -f settings.sh ]
then
    source settings.sh 
fi
if [ "${*}" != "" ]
then
   ARGS="${*}"
else
   ARGS="Shared.v JsSyntax.v JsSyntaxAux.v JsSemantics.v JsReduction.v JsSemanticsAux.v JsSafety.v JsWf.v JsScopes.v JsInterpreter.v JsInterpreterProofs.v"
fi
#FLOCQ_INC="-I ${FLOCQ}/src/Appli -I ${FLOCQ}/src/Calc -I ${FLOCQ}/src/Core -I ${FLOCQ}/src/Prop"
FLOCQ_INC="-R ${FLOCQ}/src Flocq"
${COQBIN}coqide -I . -I ${TLC} ${FLOCQ_INC} ${ARGS} &

