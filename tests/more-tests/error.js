
// @negative

function $ERROR (str) {
try {
var local = __$ERROR__
__$ERROR__ = local + str
}
catch(ex) {
 __$ERROR__ = str
}
}

$ERROR("foo")
$ERROR("bar")

