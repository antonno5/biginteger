#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <complex>
#include <cmath>

class BigInteger {
    std::vector<long long> m_digits;
    bool m_is_positive = false;

    static const size_t LOG_MOD = 4;
    static const long long MOD = 1e4;
    static const long long BASE = 10;

    BigInteger abs() const {
        BigInteger copy = *this;
        copy.m_is_positive = true;
        return copy;
    }

    static std::string digit2string(long long x, bool save_nulls) {
        std::string ans = std::to_string(x);
        if (!save_nulls) {
            return ans;
        }
        return std::string(LOG_MOD - ans.size(), '0') + ans;
    }

    void check_null() {
        if (!(*this)) {
            m_is_positive = true;
        }
    }

    void delete_leading_nulls() {
        while ((m_digits.back() == 0LL) && (m_digits.size() > 1)) {
            m_digits.pop_back();
        }
    }

    void check() {
        delete_leading_nulls();
        check_null();
    }

    std::strong_ordering compare(const BigInteger& that, bool check_sign)  const {
        if (m_digits.size() != that.m_digits.size()) {
            if ((m_digits.size() < that.m_digits.size()) ^ (check_sign ? (!m_is_positive) : 0)) {
                return std::strong_ordering::less;
            }
            else {
                return std::strong_ordering::greater;
            }
        }
        for (size_t i = m_digits.size() - 1; i < m_digits.size(); --i) {
            if (m_digits[i] != that.m_digits[i]) {
                return (check_sign && !m_is_positive) ? (that.m_digits[i] <=> m_digits[i]) :
                       (m_digits[i] <=> that.m_digits[i]);
            }
        }
        return std::strong_ordering::equal;
    }

    BigInteger& addition(const BigInteger& that, bool is_add) {
        long long remainder = 0;
        for (size_t i = 0; remainder != 0 || i < std::max(m_digits.size(), that.m_digits.size()); ++i) {
            if (i == m_digits.size()) {
                m_digits.push_back(0);
            }
            remainder += m_digits[i] + ((i < that.m_digits.size()) ? that.m_digits[i] : 0)
                                       * (is_add ? 1 : -1);
            if (remainder < 0) {
                remainder += MOD;
                m_digits[i + 1] -= 1;
            }
            m_digits[i] = remainder % MOD;
            remainder /= MOD;
        }
        check();
        return *this;
    }

    static size_t reverseBits(size_t i, size_t cup) {
        size_t res = 0;
        for (size_t bit = 1; bit < cup; bit <<= 1) {
            if (i & bit) {
                res += (cup / bit) / 2;
            }
        }
        return res;
    }

    using cld = std::complex<long double>;

    static void fft(cld* a, size_t n, cld q) {
        if(n == 1) {
            return;
        }

        for (size_t j = 1; j < n; ++j) {
            size_t revj = reverseBits(j, n);
            if (j < revj) {
                std::swap(a[j], a[revj]);
            }
        }

        cld* aend = a + n;
        for (size_t l = 2; l <= n; l <<= 1) {
            cld cq = 1;
            for (size_t ll = 0; ll < n / l; ++ll) {
                cq *= q;
            }

            for (cld *st = a; st != aend; st += l) {
                cld* mid = st + l / 2;
                cld cqdeg = 1;

                for(cld* ufl = st, *ukr = mid; ufl != mid; ++ufl, ++ukr) {
                    cld u = *ufl;
                    cld v = *ukr * cqdeg;
                    *ufl = u + v;
                    *ukr = u - v;
                    cqdeg *= cq;
                }
            }
        }
    }

    static void invFFT(cld* a, size_t n, cld q) {
        fft(a, n, q);
        for (size_t j = 0; j < n; ++j) {
            a[j] /= n;
        }
    }

    static std::vector<long long> mulPolynoms(const std::vector<long long> &a,
                                              const std::vector<long long> &b) {
        size_t n = 1;
        while (n < a.size() || n < b.size()) {
            n *= 2;
        }
        n *= 2;

        cld *ca = new cld[n];
        cld *cb = new cld[n];
        fill(ca, ca + n, cld(0));
        fill(cb, cb + n, cld(0));
        for (size_t i = 0; i < a.size(); ++i) {
            ca[i] = cld(a[i]);
        }
        for (size_t i = 0; i < b.size(); ++i) {
            cb[i] = cld(b[i]);
        }

        static const long double PI_2 = 2.0l * acosl(-1.0l);
        long double ang = PI_2 / n;
        cld q(cosl(ang), sinl(ang));

        fft(ca, n, q);
        fft(cb, n, q);

        for (size_t i = 0; i < n; ++i) {
            ca[i] *= cb[i];
        }

        invFFT(ca, n, std::conj(q));

        std::vector<long long> ans(a.size() + b.size() - 1, 0);
        for (size_t i = 0; i < ans.size(); ++i) {
            ans[i] = static_cast<long long>(roundl(ca[i].real()));
        }

        delete[] ca;
        delete[] cb;

        return ans;
    }

    BigInteger multiply(long long x, size_t shift) const {
        BigInteger ans;
        ans.m_digits.pop_back();
        for (size_t i = 0; i < shift; ++i) {
            ans.m_digits.push_back(0);
        }
        long long remainder = 0;
        for (size_t i = 0; i < m_digits.size() || remainder != 0; ++i) {
            remainder += (i < m_digits.size() ? m_digits[i] * x : 0);
            ans.m_digits.push_back(remainder % MOD);
            remainder /= MOD;
        }
        ans.check();
        return ans;
    }

    long long bin_division(const BigInteger& that, size_t shift) const {
        int l = 0, r = MOD;
        while (l + 1 != r) {
            int m = (l + r) / 2;
            auto now = that.multiply(m, shift);
            if (compare(now, false) == std::strong_ordering::less) {
                r = m;
            }
            else {
                l = m;
            }
        }
        return l;
    }
public:

    BigInteger() : m_digits(std::vector<long long>(1,0)), m_is_positive(true) {}

    BigInteger(long long x) : m_is_positive(x >= 0) {
        x = llabs(x);
        if (!x) {
            m_digits.push_back(0);
            return;
        }
        while (x) {
            m_digits.push_back(x % MOD);
            x /= MOD;
        }
    }

    BigInteger(const std::string& input) : m_is_positive(input[0] != '-') {
        long long pow_BASE = 1;
        m_digits.push_back(0);
        for (int i = static_cast<int>(input.size()) - 1; i >= 0 + static_cast<int>(input[0] == '-');
             --i) {
            if (pow_BASE == BigInteger::MOD) {
                pow_BASE = 1;
                m_digits.push_back(0);
            }
            m_digits.back() += (input[static_cast<size_t>(i)] - '0') * pow_BASE;
            pow_BASE *= BASE;
        }
        check();
    }

    std::string toString() const {
        if (!(*this)) {
            return "0";
        }
        std::string ans;
        if (!m_is_positive) {
            ans += '-';
        }
        ans += BigInteger::digit2string(m_digits.back(), false);
        for (size_t i = m_digits.size() - 2; i < m_digits.size(); --i) {
            ans += digit2string(m_digits[i], true);
        }
        return ans;
    }

    explicit operator bool() const {
        return !((m_digits.size() == 1LL) && (m_digits[0] == 0LL));
    }

    explicit operator double() const {
        double ans = 0;
        double pow_MOD = 1;
        for (long long m_digit : m_digits) {
            ans += static_cast<double>(m_digit) * pow_MOD;
            pow_MOD *= static_cast<double>(MOD);
        }
        return ans * (m_is_positive ? 1.0 : -1.0);
    }

    BigInteger operator-() const {
        BigInteger that = *this;
        that.m_is_positive ^= 1;
        that.check_null();
        return that;
    }

    bool operator==(const BigInteger& that) const = default;

    std::strong_ordering operator<=>(const BigInteger& that) const {
        if (m_is_positive != that.m_is_positive) {
            return m_is_positive <=> that.m_is_positive;
        }
        return compare(that, true);
    }

    BigInteger& operator+=(const BigInteger& that) {
        if (m_is_positive == that.m_is_positive) {
            addition(that, true);
        }
        else if (compare(that, false) == std::strong_ordering::less) {
            BigInteger copy = that;
            std::swap(*this, copy);
            *this += copy;
        }
        else {
            addition(that, false);
        }
        return *this;
    }

    BigInteger& operator-=(const BigInteger& that) {
        *this += -that;
        return *this;
    }

    BigInteger& operator*=(const BigInteger& that) {
        this->m_digits = mulPolynoms(this->m_digits, that.m_digits);
        m_is_positive = (!m_is_positive) ^ that.m_is_positive;
        for (size_t i = 0; i < m_digits.size(); ++i) {
            if (m_digits[i] >= MOD) {
                if (i == m_digits.size() - 1) {
                    m_digits.push_back(0);
                }
                m_digits[i + 1] += m_digits[i] / MOD;
                m_digits[i] = m_digits[i] % MOD;
            }
        }
        check();
        return *this;
    }

    BigInteger& operator/=(const BigInteger& that) {
        m_is_positive ^= !that.m_is_positive;
        BigInteger remainder = *this;
        for (size_t i = m_digits.size() - 1; i < m_digits.size(); --i) {
            long long x = remainder.bin_division(that, i);
            m_digits[i] = x;
            BigInteger sub = that.multiply(x, i);
            sub.m_is_positive = !m_is_positive;
            remainder += sub;
        }
        check();
        return *this;
    }

    BigInteger& operator%=(const BigInteger& that) {
        auto copy = *this;
        *this -= ((copy /= that) *= that);
        return *this;
    }

    BigInteger& operator++() {
        return (*this += BigInteger(1));
    }

    BigInteger operator++(int) {
        BigInteger past = *this;
        ++(*this);
        return past;
    }

    BigInteger& operator--() {
        return (*this += BigInteger(-1));
    }

    BigInteger operator--(int) {
        BigInteger past = *this;
        --(*this);
        return past;
    }
};

BigInteger operator+(const BigInteger& first, const BigInteger& second) {
    auto copy = first;
    return copy += second;
}

BigInteger operator-(const BigInteger& first, const BigInteger& second) {
    auto copy = first;
    return copy -= second;
}

BigInteger operator*(const BigInteger& first, const BigInteger& second) {
    auto copy = first;
    return copy *= second;
}

BigInteger operator/(const BigInteger& first, const BigInteger& second) {
    auto copy = first;
    return copy /= second;
}

BigInteger operator%(const BigInteger& first, const BigInteger& second) {
    auto copy = first;
    return copy %= second;
}

std::ostream& operator<<(std::ostream& cout, const BigInteger& x) {
    return cout << x.toString();
}

std::istream& operator>>(std::istream& cin, BigInteger& x) {
    std::string input;
    cin >> input;
    x = BigInteger(input);
    return cin;
}

BigInteger operator ""_bi(unsigned long long x) {
    return {static_cast<long long>(x)};
}

BigInteger operator ""_bi(const char* x) {
    return {x};
}

class Rational {
    BigInteger numerator;
    BigInteger denominator;

    static int sign(const BigInteger& x) {
        return static_cast<int>(x >= 0) * 2 - 1;
    }

    static BigInteger abs(const BigInteger& x) {
        return x * sign(x);
    }

    void multiply(const BigInteger& that) {
        numerator *= that;
        denominator *= that;
    }

    void same_denominator(Rational& that) {
        auto copy_denominator = denominator;
        multiply(that.denominator);
        that.multiply(copy_denominator);
    }

    Rational reverse() const {
        return Rational(denominator * sign(numerator), abs(numerator));
    }

    static BigInteger gcd(BigInteger first, BigInteger second) {
        while (second) {
            first %= second;
            std::swap(first, second);
        }
        return first;
    }

    void division_gcd() {
        auto m_gcd = gcd(abs(numerator), denominator);
        numerator /= m_gcd;
        denominator /= m_gcd;
    }
public:
    Rational() : numerator(0), denominator(1) {}
    Rational(long long x) : numerator(x), denominator(1) {}
    Rational(const BigInteger& x) : numerator(x), denominator(1) {}

    Rational operator-() const {
        Rational answer(-numerator, denominator);
        return answer;
    }

    Rational(const BigInteger& first, const BigInteger& second) : numerator(first), denominator(second) {
        division_gcd();
    }

    Rational& operator*=(const Rational& that) {
        numerator *= that.numerator;
        denominator *= that.denominator;
        division_gcd();
        return *this;
    }

    Rational& operator/=(const Rational& that) {
        return *this *= that.reverse();
    }

    Rational& operator+=(const Rational& that) {
        Rational copy = that;
        same_denominator(copy);
        numerator += copy.numerator;
        division_gcd();
        return *this;
    }

    Rational& operator-=(const Rational& that) {
        return *this += (-that);
    }

    std::string toString() const {
        std::string ans = numerator.toString();
        if (denominator != 1) {
            ans += '/' + denominator.toString();
        }
        return ans;
    }

    std::string asDecimal(size_t precision = 0) const {
        std::string ans;
        if (sign(numerator) != sign(denominator)) {
            ans += '-';
        }
        auto abs_numerator = abs(numerator);
        ans += (abs_numerator / denominator).toString();
        BigInteger remainder = (abs_numerator % denominator);
        if (precision == 0) {
            return ans;
        }
        ans += '.';
        const int BASE = 10;
        for (size_t i = 0; i < precision; ++i) {
            remainder *= BASE;
            ans += ((remainder / denominator) % BASE).toString();
            remainder %= denominator;
        }
        return ans;
    }

    explicit operator double() const {
        return double(numerator) / double(denominator);
    }

    bool operator==(const Rational& that) const = default;

    std::strong_ordering operator<=>(const Rational& that) const {
        Rational copy_this = *this;
        Rational copy_that = that;
        copy_this.same_denominator(copy_that);
        return copy_this.numerator <=> copy_that.numerator;
    }
};

Rational operator+(const Rational& first, const Rational& second) {
    auto copy = first;
    return copy += second;
}

Rational operator-(const Rational& first, const Rational& second) {
    auto copy = first;
    return copy -= second;
}

Rational operator*(const Rational& first, const Rational& second) {
    auto copy = first;
    return copy *= second;
}

Rational operator/(const Rational& first, const Rational& second) {
    auto copy = first;
    return copy /= second;
}
