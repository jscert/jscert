function foo() {
    for (var x in this) {
        print(x)
    }
}
foo()
print("passed.");
