TLC=lib/tlc/src
FLOCQ=lib/flocq
COQBIN=
if [ -f settings.sh ]
then
    source settings.sh 
fi
if [ "${*}" != "" ]
then
   if [ -f settings.sh ]
	then
		ARGS="${*}"
	else
		ARGS="${*}"
	fi
else
   ARGS="coq/JsSyntax.v	coq/JsPreliminary.v coq/JsPrettyInterm.v	coq/JsPrettyRules.v coq/JsCorrectness.v coq/JsInit.v"
fi
#FLOCQ_INC="-I ${FLOCQ}/src/Appli -I ${FLOCQ}/src/Calc -I ${FLOCQ}/src/Core -I ${FLOCQ}/src/Prop"
FLOCQ_INC="-R ${FLOCQ}/src Flocq"
${COQBIN}coqide -I . -I ${TLC} ${FLOCQ_INC} ${ARGS} &


