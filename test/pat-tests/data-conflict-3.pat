# should fail: two user-defined types with same constructor name
data Foo a = MkFoo a
data Bar a = MkFoo a

def main(): Unit { () }
main()

