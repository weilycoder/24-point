# 24点计算器

利用DFS解24点问题。

## 支持的运算符

+ 四则运算
+ 阶乘
+ 平方根
+ 数字拼接

## 使用方法

编译后直接运行：

```text
demo
```

程序将不断读入数字，然后尝试用这些数字计算出24。程序将计算到的第一个结果输出。

可以用`-d`设置数据：

```text
test -d 2 3 1 0
```

程序直接输出结果（对于以上数据，输出`(sqrt(0+1+3)+2)!`）。
`-d`使程序不断尝试解析其后的数据，直到失败。
**不要**用双引号包含数据，这将导致解析失败。

可以用`f`、`-s`和`-c`分别禁止阶乘、平方根和字符拼接：

```text
test -d 2 3 1 0 -s
```

*Output:*

```text
(((0+1)*3)!-2)!
```

或者：

```text
test -d 2 3 1 0 -s -f
```

*Output:*

```text
3*(10-2)
```

如果找不到解，输出`N/A`。

```text
test -d 2 3 1 0 -s -f -c
```

*Output:*

```text
N/A
```

程序解析命令行失败后，行为与直接运行时一致。

*注意：程序不支持输入负数。*
