class Test1{
	public void bar(){
		System.out.println("Test bar");
	}
	public static void main(String[] args) {
		Test1 a,b;
		for(int i=0;i<100000;++i){
			if(i%2==0){
				a=new Test1();
			}
			else a=new Test2();
			a.bar();
			b=new Test1();
			b.bar();
		}
	}
}
class Test2 extends Test1{
	public void bar(){
		System.out.println("Test2 bar");
	}
}
class Test3 extends Test1{
	public void bar(){
		System.out.println("Test3 bar");
	}
}
