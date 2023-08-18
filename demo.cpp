#include "bigint_dec.h"
#include <iostream>
#include <stack>
#define MAX_BIGINT_SIZE 8
using namespace std;

typedef stack<BigInt> st_int;
typedef stack<bool> st_bool;
typedef stack<string> st_str;
typedef vector<BigInt> v_int;

const char ops[8] = {'+', '-', '*', '/', '|', '!', 's'};

short STATE = 0;
const BigInt zero(0), one(1), minusone(-1), two(2), goal(24);

inline BigInt safe_add(BigInt a, BigInt b) {
	BigInt x = a + b;
	if (x.get_size() > MAX_BIGINT_SIZE) return minusone;
	return x;
}

inline BigInt safe_sub(BigInt a, BigInt b) {
	BigInt x = a - b;
	if (x < zero) return minusone;
	return x;
}

inline BigInt safe_mul(BigInt a, BigInt b) {
	BigInt x = a * b;
	if (x.get_size() > MAX_BIGINT_SIZE) return minusone;
	return x;
}

inline BigInt safe_div(BigInt a, BigInt b) {
	if (b.is_zero()) return minusone;
	if (!(a % b).is_zero()) return minusone;
	return a / b;
}

BigInt factorial(BigInt x) {
	if (STATE & 1) return minusone;
	if (x.is_zero()) return one;
	if (x <= two) return minusone;
	BigInt ans = one;
	for (BigInt i = x; i > one; i -= one) {
		ans *= i;
		if (ans.get_size() > MAX_BIGINT_SIZE) return minusone;
	}
	return ans;
}

BigInt isqrt_newton(BigInt n) {
	if (STATE & 2) return minusone;
	if (n < two) return minusone;
	BigInt x;
	x.set_bysize(n.get_size() >> 1);
	bool decreased = false;
	for (;;) {
		BigInt nx = (x + n / x) /= two;
		if (x == nx || (nx > x && decreased)) break;
		decreased = nx < x;
		x = nx;
	}
	if (x * x == n) return x;
	return minusone;
}

BigInt connect(BigInt a, BigInt b) {
	BigInt r(a.to_str() + b.to_str());
	if (r.get_size() > MAX_BIGINT_SIZE) return minusone;
	return r;
}

char push_op_1(st_int &st, char op, st_bool &tp) {
	if (st.empty()) return -1;
	BigInt a = st.top();
	st.pop();
	switch (op) {
		case 5:
			st.push(factorial(a));
			break;
		case 6:
			st.push(isqrt_newton(a));
			break;
	}
	tp.pop();
	tp.push(false);
	if (st.top() < zero) return -3;
	return 0;
}

char push_op_2(st_int &st, char op, st_bool &tp) {
	if (st.size() < 2) return -1;
	BigInt a = st.top(), b;
	st.pop();
	b = st.top();
	st.pop();
	bool flag = tp.top();
	tp.pop();
	flag &= tp.top();
	tp.pop();
	switch (op) {
		case 0:
			st.push(safe_add(a, b));
			break;
		case 1:
			st.push(safe_sub(a, b));
			break;
		case 2:
			st.push(safe_mul(a, b));
			break;
		case 3:
			st.push(safe_div(a, b));
			break;
		case 4:
			if (!(STATE & 4) & flag) st.push(connect(a, b));
			else return -2;
			break;
		default:
			return -2;
	}
	tp.push(op == 4);
	if (st.top() < zero) return -3;
	return 0;
}

char push_op(st_int &st, char op, st_bool &tp) {
	switch (op) {
		case 5:
		case 6:
			return push_op_1(st, op, tp);
		default:
			return push_op_2(st, op, tp);
	}
}

inline st_str &push(st_str &st, string s) {
	st.push(s);
	return st;
}

st_str dfs(v_int &data, st_int &st, st_bool &tp) {
	st_str r;
	if (data.empty() && st.size() == 1 && st.top() == goal) return r;
	r.push("N/A");
	for (int i = 0; i < (int)data.size(); ++i) {
		if (data[i] < zero) return r;
		v_int tmp_v;
		st_int tmp_st = st;
		st_bool ttp = tp;
		tmp_st.push(data[i]), ttp.push(true);
		for (int j = 0; j < (int)data.size(); ++j) {
			if (i == j) continue;
			tmp_v.push_back(data[j]);
		}
		st_str ans = dfs(tmp_v, tmp_st, ttp);
		if (ans.empty() || ans.top() != "N/A") return push(ans, data[i].to_str());
	}
	for (int i = 0; i < 7; ++i) {
		st_int tmp_st = st;
		st_bool ttp = tp;
		if (push_op(tmp_st, i, ttp) == 0) {
			st_str ans = dfs(data, tmp_st, ttp);
			if (ans.empty() || ans.top() != "N/A") return push(ans, string(1, ops[i]));
		}
	}
	return r;
}

inline string _bracket(string a) { return "(" + a + ")"; }
string bracket(string a, string ops) {
	int flag = 0;
	for (int i = 0; i < (int)a.length(); ++i) {
		if (a[i] == '(') flag++;
		else if (a[i] == ')') flag--;
		if (!flag && (ops.find(a[i]) != string::npos))
			return _bracket(a);
	}
	return a;
}
inline string bracket_mul(string a) { return bracket(a, "+-"); }
inline string bracket_mul2(string a) { return bracket(a, "+-*/"); }
inline string bracket_fac(string a) { return bracket(a, "+-*/!"); }

void push_op(st_str &st, char op) {
	string a = st.top();
	st.pop();
	if (op == '!') {
		st.push(bracket_fac(a) + "!");
		return;
	} else if (op == 's') {
		st.push("sqrt(" + a + ")");
		return;
	}
	string b = st.top();
	st.pop();
	switch (op) {
		case '+':
			st.push(a + "+" + b);
			break;
		case '-':
			st.push(a + "-" + bracket_mul(b));
			break;
		case '*':
			st.push(bracket_mul(a) + "*" + bracket_mul(b));
			break;
		case '/':
			st.push(bracket_mul(a) + "/" + bracket_mul2(b));
			break;
		case '|':
			st.push(a + b);
			break;
	}
}

bool is_int(string str) {
	for (int i = 0; i < (int)str.length(); ++i)
		if (str[i] < '0' || str[i] > '9')
			return false;
	return true;
}

string solve(v_int &data) {
	st_int st;
	st_bool tp;
	st_str ans = dfs(data, st, tp);
	if (ans.size() && ans.top() == "N/A") return "N/A";
	st_str tmp;
	BigInt r;
	for (; ans.size(); ans.pop()) {
		if (is_int(ans.top())) tmp.push(ans.top());
		else push_op(tmp, ans.top()[0]);
	}
	return tmp.top();
}

int main(int argc, char *argv[]) {
	BigInt t;
	v_int data;
	for (int i = 1; i < argc; ++i) {
		if (strcmp(argv[i], "-f") == 0)
			STATE |= 1;
		else if (strcmp(argv[i], "-s") == 0)
			STATE |= 2;
		else if (strcmp(argv[i], "-c") == 0)
			STATE |= 4;
		else if (strcmp(argv[i], "-d") == 0) {
			int j = i + 1;
			for (; j < argc; ++j) {
				if (is_int(argv[j])) data.push_back(t.from_str(argv[j]));
				else break;
			}
			i = j - 1;
		} else {
			STATE = 0;
			data.clear();
			break;
		}
	}
	if (!data.size()){
		string s;
		while (cin >> s && is_int(s)) data.push_back(t.from_str(s));
	}
	cout << solve(data) << endl;
	return 0;
}
