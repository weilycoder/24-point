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
const int solve_queue[6] = {7, 3, 6, 5, 4, 0};
const BigInt zero(0), one(1), minusone(-1), two(2), ten(10), goal(24);

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
	if (STATE & 4) return minusone;
	if (a.is_zero()) return minusone;
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
			if (flag) st.push(connect(a, b));
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

string solve(v_int &data, int state) {
	STATE = state;
	return solve(data);
}

void solve(BigInt a, BigInt b, BigInt c, BigInt d) {
	v_int v;
	v.push_back(a);
	v.push_back(b);
	v.push_back(c);
	v.push_back(d);
	cout << a.to_str() << b.to_str() << c.to_str() << d.to_str() << " ";
	string ans = solve(v, 7);
	for (int i = 1; ans == "N/A" && i < 6; ++i)
		ans = solve(v, solve_queue[i]);
	cout << ans << endl; 
}

int main() {
	for (BigInt a = zero; a < ten; a += one)
		for (BigInt b = a; b < ten; b += one)
			for (BigInt c = b; c < ten; c += one)
				for (BigInt d = c; d < ten; d += one)
					solve(a, b, c, d);
	return 0;
}
