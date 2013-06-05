var didAnything = false;

for (var x in undefined) {
  didAnything = true;
}

for (var x in null) {
  didAnything = true;
}

if (!didAnything) {
  print('passed');
}
