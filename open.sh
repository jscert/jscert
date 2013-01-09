TLC=coq/tlc
FLOCQ=coq/flocq
COQBIN=
if [ -f settings.sh ]
then
    source settings.sh 
fi
if [ "${*}" != "" ]
then
   ARGS="${*}"
else
   ARGS="coq/Shared.v coq/JsSyntax.v coq/JsSemanticsDefs.v coq/JsSemanticsRules.v"
fi
#FLOCQ_INC="-I ${FLOCQ}/src/Appli -I ${FLOCQ}/src/Calc -I ${FLOCQ}/src/Core -I ${FLOCQ}/src/Prop"
FLOCQ_INC="-R ${FLOCQ}/src Flocq"
${COQBIN}coqide -I . -I ${TLC} ${FLOCQ_INC} ${ARGS} &

