class Test{
	public void bar(){
		System.out.println("Test bar");
	}
	public static void main(String[] args) {
		Test a,b;
		for(int i=0;i<20000000;++i){
			if(i%2==0){
				a=new Test();
			}
			else a=new Test2();
			a.bar();
			b=new Test();
			b.bar();
		}
	}
}
class Test2 extends Test{
	public void bar(){
		System.out.println("Test2 bar");
	}
}
