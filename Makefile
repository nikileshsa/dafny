
default:
	( cd /Users/davidcok/yucca/dafny;  msbuild Source/Dafny.sln )

clean:
	( cd /Users/davidcok/yucca/dafny; rm -rf Source/Dafny/bin/Debug )

all:
	( cd /Users/davidcok/yucca/dafny; rm -rf Source/Dafny/bin/Debug; msbuild Source/Dafny.sln )
