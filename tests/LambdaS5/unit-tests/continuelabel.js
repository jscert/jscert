var __str="", toadd;

outer : for(var index=0; index<4; index+=1) {
    nested : for(var index_n=0; index_n<=index; index_n++) {
	if (index*index_n == 6)continue nested;
        toadd = "" + index;
        toadd += index_n;
        __str += toadd;
    } 
}

if (__str === "001011202122303133") {
  print("passed");
}
