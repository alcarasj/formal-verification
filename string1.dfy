method isPrefix(pre: seq<char>, str: seq<char>) returns (res: bool)
	requires |pre| > 0 && |str| >= |pre|
{
	var i := 0;
	while i < |pre|
		invariant i >= 0
		{
			if pre[i] == str[i]	
			{ 
				res := true; 
			}
			else 
			{
				return false;
			}
			i := i + 1;
		}
}

method isSubString(sub: seq<char>, str: seq<char>) returns (res: bool)
	requires |sub| > 0 && |str| >= |sub|
{
	var isPrefix := isPrefix(sub, str);
	if isPrefix
	{
		return true;
	}
	res := false;
	var i := 0;
	var j := 0;
	while i < |str|
		invariant i >= 0
	{
		if j < |sub|
		{
			if str[i] == sub[j] 
			{
				j := j + 1;
			}
		}
		else
		{
			j := 0;
		}
		if j == |sub| 
		{
			return true;
		}
		i := i + 1;
	}
}

method haveCommonKSubstring(k: nat, str1: seq<char>, str2: seq<char>) returns (found: bool)
	requires |str1| > 0 && |str2| > 0
{
	var i := 0;
	if |str1| > |str2|
	{
		while i < |str1|
			invariant i >= 0
		{
			

			i := i + 1;
		}
	}
	else
	{
		while i < |str2|
			invariant i >= 0
		{
			
			i := i + 1;
		}
	}
}

method maxCommonSubstringLength(str1: seq<char>, str2: seq<char>) returns (len: nat)
	requires |str1| > 0 && |str2| > 0
{
	
}