
a:  while (true) {
    b:  while (true) {
        break a ;
        $ERROR ("#1.1:  Break didn't worked.")
    } ;
    $ERROR ("#1.2:  Wrong break label.")
}

