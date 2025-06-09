a := 1;

if ( true ) {
	print ( a - 1); 
	local a := 2;
	a := 3;
	print ( a - 3 );
	if(true){
		a := 4;
		a := 5;
		print(a - 5);
		local a := 6;
		print(a - 6);
	}
	print(a - 5);
}
print ( a - 1 );