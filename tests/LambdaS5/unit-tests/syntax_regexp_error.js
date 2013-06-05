try {
	new RegExp("++a");
} catch (e) {
	if (e instanceof SyntaxError) {
    console.log('Passed.');
	}
  else {
    console.log('Expected SyntaxError, got ' + e);
  }
}
