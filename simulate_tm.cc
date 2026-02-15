#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <random>
#include <functional>
#include <string>


class GeneralizedShiftMap {
  private:
    std::function<int(std::vector<bool>, int)> shift;
    std::function<std::vector<bool>(std::vector<bool>, int)> overwrite;
    std::vector<bool> a;
    int pt;
  
  public:
    GeneralizedShiftMap(
        std::function<int(std::vector<bool>, int)> shift,
        std::function<std::vector<bool>(std::vector<bool>, int)> overwrite,
        std::vector<bool> initial_vector,
        int initial_point
    ) : shift(shift), overwrite(overwrite), a(initial_vector), pt(initial_point) {
    }

    void next() {
        int d = shift(a, pt);
        a = overwrite(a, pt);
        pt += d;
    }

    std::vector<bool> get_subsequence(int begin, int end) {
        std::vector<bool> subsequence(a.begin() + pt + begin, a.begin() + pt + end);
        return subsequence;
    }

    std::vector<bool> get_vector() { return a; }

    int get_point() { return pt; }

    int get_size() { return a.size(); }

    void print_vector() {
        for(auto&& e : a) {
            std::cout << (e ? " " : "*");
        }
        std::cout << std::endl;
    }
};


/******** Functions which convert Turing machines to generalized shift maps ********/

int64_t neighborhood_int(std::vector<bool> v, int pt, int begin, int end) {
    int64_t r = 0;
    for (int i = 0; i < end-begin+1; i++) {
        r += (1LL << i) * v[pt + end - i];
    }
    return r;
}

void overwrite_int(std::vector<bool> &v, int pt, int begin, int end, int64_t num) {
    for (int i = 0; i < end-begin+1; i++) {
        v[pt + end - i] = num % 2;
        num /= 2;
    }
}

int f(std::vector<std::vector<int>> shift, std::vector<bool> a, int pt) {
    const int n_states = shift.size();
    const int n_symbols = shift[0].size();
    const int n_digits = (int)std::ceil(std::log2(std::max(n_states, n_symbols)));

    const int begin = 0;
    const int end = n_digits * 2 - 1;

    int neighborhood = neighborhood_int(a, pt, begin, end);
    return n_digits * shift[neighborhood >> n_digits][neighborhood & ((1 << n_digits) - 1)];
}

std::vector<bool> g(std::vector<std::vector<int>> state_change, std::vector<std::vector<int>> overwrite, std::vector<std::vector<int>> shift, std::vector<bool> a, int pt) {
    const int n_states = state_change.size();
    const int n_symbols = state_change[0].size();
    const int n_digits = (int)std::ceil(std::log2(std::max(n_states, n_symbols)));

    int begin = -n_digits;
    int end = n_digits * 2 - 1;
    auto b = a;

    int64_t neighborhood = neighborhood_int(a, pt, begin, end);
    int t = overwrite[(neighborhood >> n_digits) & ((1 << n_digits) - 1)][neighborhood & ((1 << n_digits) - 1)];
    int s = state_change[(neighborhood >> n_digits) & ((1 << n_digits) - 1)][neighborhood & ((1 << n_digits) - 1)];

    int w = f(shift, a, pt) / n_digits;
    overwrite_int(b, pt, n_digits, n_digits * 2 - 1, t);
    if (w >= 0) {
        begin = 0;
        end = (w+1) * n_digits - 1;
        neighborhood = neighborhood_int(b, pt, begin, end);
        overwrite_int(b, pt, begin, end, (neighborhood << n_digits) + s);
    } else {
        begin = w * n_digits;
        end = n_digits - 1;
        neighborhood = neighborhood_int(b, pt, begin, end);
        overwrite_int(b, pt, begin, end, (s << (-w) * n_digits) + (neighborhood >> n_digits));
    }
    return b;
}

std::vector<bool> generate_vector(unsigned long num, int size) {
    std::vector<bool> v(size);
    for (int i = 0; i < size; i++) {
        v[size -1 -i] = num % 2;
        num /= 2;
    }
    return v;
}

std::vector<bool> initial_vector(int n_digits, int init_state, std::vector<int> init_tape, int init_pos) {
    std::vector<bool> r = {};
    for (int i = 0; i < init_tape.size(); i++) {
        if (i == init_pos) {
            auto state_vec = generate_vector(init_state, n_digits);
            r.insert(r.end(), state_vec.begin(), state_vec.end());
        }
        auto symbol_vec = generate_vector(init_tape[i], n_digits);
        r.insert(r.end(), symbol_vec.begin(), symbol_vec.end());
    }
    return r;
}


/******** Helpers ********/

uint64_t get_rand_range(uint64_t min_val, uint64_t max_val) {
    static std::mt19937_64 mt64(23);
    std::uniform_int_distribution<uint64_t> get_rand_uni_int(min_val, max_val);

    return get_rand_uni_int(mt64);
}

int64_t vector_to_num(std::vector<bool> v) {
    int64_t r = 0;
    for (int i = 0; i < v.size(); i++) {
        r += (1LL << i) * v[v.size() - 1 - i];
    }
    return r;
}

std::vector<int> decode(int n_digits, std::vector<bool> v) {
    std::vector<int> r = {};
    int val = 0;
    for (int i = 0; i < v.size(); i++) {
        val += v[i] << (n_digits - 1 - (i % n_digits));
        if ((i+1) % n_digits == 0) {
            r.emplace_back(val);
            val = 0;
        }
    }
    return r;
}

void print_usage() {
    std::cout << "usage: ./a.out <sort|lccp|wolfram> [STEPS]\n";
}


/******** Main function converts a Turing machine to a generalized shift map, and simulate it. ********/

int main(int argc, char** argv) {
    int STEPS;
    if (argc == 2) {
        STEPS = 1000000;
    } else if (argc == 3) {
        STEPS = std::stoi(argv[2]);
    } else {
        print_usage();
        return 1;
    }
    const std::string MACHINE = argv[1];


    // Definition of Turing machine
    std::vector<std::vector<int>> state_change;
    std::vector<std::vector<int>> overwrite;
    std::vector<std::vector<int>> shift;
    int initial_state;
    int accepting_state;
    int initial_pos;
    std::vector<int> initial_tape = {};

    if (MACHINE == "sort") {
        // Insertion sort
        state_change = {
            { 1,  2, 31},
            { 3, 11, 31},
            { 0,  3, 31},
            { 4,  5, 31},
            { 6, 11, 31},
            { 0,  6, 31},
            { 7,  8, 31},
            { 9, 11, 31},
            { 0,  9, 31},
            {10,  0, 31},
            { 0, 11, 31},
            {12, 13, 31},
            {14, 15, 31},
            {14, 15, 31},
            {16, 16, 31},
            {16, 16, 31},
            {17, 18, 31},
            {19, 20, 31},
            {19, 20, 31},
            {21, 21, 31},
            {21, 21, 31},
            {22, 23, 31},
            {24, 25, 31},
            {24, 25, 31},
            {26, 26, 31},
            {26, 26, 31},
            {27, 28, 31},
            {29, 30, 31},
            {29, 30, 31},
            { 0,  0, 31},
            { 0,  0, 31},
            {31, 31, 31}
        };
        overwrite = {
            {0, 1, 2},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 0, 0},
            {1, 1, 0},
            {0, 1, 2}
        };
        shift = {
            {-4, -4, 0},
            { 5,  0, 0},
            { 8,  5, 0},
            {-4, -4, 0},
            { 5, -1, 0},
            { 7,  5, 0},
            {-4, -4, 0},
            { 5, -2, 0},
            { 6,  5, 0},
            {-4,  1, 0},
            { 5, -3, 0},
            { 4,  4, 0},
            {-4, -4, 0},
            {-4, -4, 0},
            { 1,  1, 0},
            { 1,  1, 0},
            { 4,  4, 0},
            {-4, -4, 0},
            {-4, -4, 0},
            { 1,  1, 0},
            { 1,  1, 0},
            { 4,  4, 0},
            {-4, -4, 0},
            {-4, -4, 0},
            { 1,  1, 0},
            { 1,  1, 0},
            { 4,  4, 0},
            {-4, -4, 0},
            {-4, -4, 0},
            {-3, -3, 0},
            {-3, -3, 0},
            { 0,  0, 0}
        };
        initial_state = 0;
        // [8,  4, 12,  4,  7,  9, 14,  9,
        //  4, 13,  5, 14, 13, 13, 10, 12,
        //  5,  6,  6, 10,  1, 15, 11,  7,
        //  8,  7,  6, 11, 13,  5,  1,  1]
        initial_tape = {
            0,  0, 0, 0, 0,
                1, 0, 0, 0,  0, 1, 0, 0,  1, 1, 0, 0,  0, 1, 0, 0,  0, 1, 1, 1,  1, 0, 0, 1,  1, 1, 1, 0,  1, 0, 0, 1,
                0, 1, 0, 0,  1, 1, 0, 1,  0, 1, 0, 1,  1, 1, 1, 0,  1, 1, 0, 1,  1, 1, 0, 1,  1, 0, 1, 0,  1, 1, 0, 0,
                0, 1, 0, 1,  0, 1, 1, 0,  0, 1, 1, 0,  1, 0, 1, 0,  0, 0, 0, 1,  1, 1, 1, 1,  1, 0, 1, 1,  0, 1, 1, 1,
                1, 0, 0, 0,  0, 1, 1, 1,  0, 1, 1, 0,  1, 0, 1, 1,  1, 1, 0, 1,  0, 1, 0, 1,  0, 0, 0, 1,  0, 0, 0, 1,
            2, 0
        };
        initial_pos = 5;
        accepting_state = 31;

    } else if (MACHINE == "lccp") {
        // Locate, Copy, Clean-up, and Perform Universal Turing machine
        state_change = {
            // Locate
            { 1,  0,  0, 28, 28,  0,  0, 28},
            { 1,  1,  1, 28, 28,  2, 28, 28},
            {10, 28, 28,  3,  4, 28, 28, 28},
            { 5, 28, 28,  3,  3, 28, 28, 28},
            { 6, 28, 28,  4,  4, 28, 28, 28},
            { 5,  7,  8,  5,  5, 28, 28, 28},
            { 6,  8,  7,  6,  6, 28, 28, 28},
            { 7,  2,  2,  7,  7, 28, 28, 28},
            { 9,  8,  8, 28, 28, 28, 28, 28},
            { 9,  9,  9,  9,  9,  2, 28, 28},
            // Copy
            {10, 11, 12, 10, 10, 28, 28, 28},
            {11, 11, 11, 11, 11, 13, 28, 28},
            {12, 12, 12, 12, 12, 14, 28, 28},
            {16, 15, 15, 13, 13, 28, 28, 28},
            {17, 15, 15, 14, 14, 28, 28, 28},
            {10, 15, 15, 28, 28, 28, 28, 28},
            // Clean-Up
            {28, 16, 16, 16, 16, 16, 18, 28},
            {28, 17, 17, 17, 17, 17, 18, 28},
            {19, 18, 18, 18, 18, 18, 28, 28},
            {19, 20, 20, 19, 19, 20, 28, 28},
            {20, 20, 20, 28, 28, 21, 28, 28},
            {22, 21, 21, 28, 28, 28, 28, 28},
            {28, 23, 24, 28, 28, 28, 28, 28},
            // Perform
            {28, 23, 23, 25, 25, 23, 28, 28},
            {28, 24, 24, 25, 25, 24, 28, 28},
            {28, 26, 27, 28, 28, 28, 28, 28},
            {28, 26, 26, 28, 28, 26, 28,  1},
            {28, 27, 27, 28, 28, 27, 28,  1},
            {28, 28, 28, 28, 28, 28, 28, 28}
        };
        overwrite = {
            // Locate
            {0, 1, 2, 0, 0, 5, 6, 0},
            {0, 3, 4, 0, 0, 5, 0, 0},
            {0, 0, 0, 1, 2, 0, 0, 0},
            {0, 0, 0, 3, 4, 5, 0, 0},
            {0, 0, 0, 3, 4, 5, 0, 0},
            {0, 3, 4, 3, 4, 0, 0, 0},
            {0, 3, 4, 3, 4, 0, 0, 0},
            {0, 1, 2, 3, 4, 0, 0, 0},
            {0, 3, 4, 0, 0, 0, 0, 0},
            {0, 3, 4, 3, 4, 5, 0, 0},
            // Copy
            {0, 3, 4, 3 ,4, 0, 0, 0},
            {0, 1, 2, 3, 4, 5, 0, 0},
            {0, 1, 2, 3, 4, 5, 0, 0},
            {0, 3, 3, 3, 4, 0, 0, 0},
            {0, 4, 4, 3, 4, 0, 0, 0},
            {0, 1, 2, 0, 0, 0, 0, 0},
            // Clean-Up
            {0, 1, 2, 3, 4, 5, 3, 0},
            {0, 1, 2, 3, 4, 5, 4, 0},
            {0, 1, 2, 1, 2, 5, 0, 0},
            {0, 1, 2, 1, 2, 5, 0, 0},
            {0, 1, 2, 0, 0, 5, 0, 0},
            {0, 1, 2, 0, 0, 0, 0, 0},
            {0, 7, 7, 0, 0, 0, 0, 0},
            // Perform
            {0, 1, 2, 1, 1, 5, 0, 0},
            {0, 1, 2, 2, 2, 5, 0, 0},
            {0, 6, 6, 0, 0, 0, 0, 0},
            {0, 1, 2, 0, 0, 5, 0, 1},
            {0, 1, 2, 0, 0, 5, 0, 2},
            {0, 0, 0, 0, 0, 0, 0, 0}
        };
        shift = {
            // Locate
            {-1,  1,  1,  0,  0,  1,  1,  0},
            {-1, -1, -1,  0,  0,  1,  0,  0},
            { 1,  0,  0,  1,  1,  0,  0,  0},
            { 1,  0,  0,  1,  1,  0,  0,  0},
            { 1,  0,  0,  1,  1,  0,  0,  0},
            { 1, -1,  1,  1,  1,  0,  0,  0},
            { 1,  1, -1,  1,  1,  0,  0,  0},
            {-1,  1,  1, -1, -1,  0,  0,  0},
            {-1,  1,  1,  0,  0,  0,  0,  0},
            {-1, -1, -1, -1, -1,  1,  0,  0},
            // Copy
            { 1, -1, -1,  1,  1,  0,  0,  0},
            {-1, -1, -1, -1, -1,  1,  0,  0},
            {-1, -1, -1, -1, -1,  1,  0,  0},
            {-1,  1,  1,  1,  1,  0,  0,  0},
            {-1,  1,  1,  1,  1,  0,  0,  0},
            { 1,  1,  1,  0,  0,  0,  0,  0},
            // Clean-Up
            { 0, -1, -1, -1, -1, -1,  1,  0},
            { 0, -1, -1, -1, -1, -1,  1,  0},
            { 1,  1,  1,  1,  1,  1,  0,  0},
            { 1, -1, -1,  1,  1, -1,  0,  0},
            {-1, -1, -1,  0,  0,  1,  0,  0},
            {-1,  1,  1,  0,  0,  0,  0,  0},
            { 0, -1, -1,  0,  0,  0,  0,  0},
            // Perform
            { 0, -1, -1, -1,  1, -1,  0,  0},
            { 0, -1, -1, -1,  1, -1,  0,  0},
            { 0,  1,  1,  0,  0,  0,  0,  0},
            { 0,  1,  1,  0,  0,  1,  0,  1},
            { 0,  1,  1,  0,  0,  1,  0,  1},
            { 0,  0,  0,  0,  0,  0,  0,  0}
        };
        initial_state = 0;
        initial_pos = 1;
        accepting_state = 28;

        initial_tape = {
            // Turing machine to simulate: decides that input is a multiple of 3

            // initial tape
            // 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5,    // 279
            1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5, // 6
            // state, read symbol
            1, 1, 1, 1, 1,    1, 0,
            // transition table                             1: left, 2: right
            1, 1, 1, 1, 1,    1,    1, 1, 1, 1, 2,    1,    2, 0,
            1, 1, 1, 1, 1,    2,    1, 1, 1, 2, 1,    2,    2, 0,
            1, 1, 1, 1, 2,    1,    1, 1, 1, 1, 1,    1,    2, 0,
            1, 1, 1, 1, 2,    2,    1, 1, 1, 2, 2,    1,    1, 0,
            1, 1, 1, 2, 1,    1,    1, 1, 1, 1, 1,    1,    2, 0,
            1, 1, 1, 2, 1,    2,    1, 1, 1, 1, 1,    2,    2, 0,
            1, 1, 1, 2, 2,    1,    1, 1, 2, 1, 2,    1,    1, 0,

            1, 1, 2, 1, 1,    1,    2, 1, 1, 1, 1,    2,    2, 0,
            1, 1, 2, 1, 1,    2,    1, 1, 2, 1, 2,    1,    1, 0,
            1, 1, 2, 1, 2,    1,    1, 2, 1, 2, 1,    1,    1, 0,
            1, 1, 2, 1, 2,    2,    1, 2, 2, 2, 1,    1,    1, 0,
            1, 1, 2, 2, 1,    1,    2, 1, 1, 1, 2,    1,    2, 0,
            1, 1, 2, 2, 1,    2,    1, 1, 2, 2, 2,    1,    1, 0,
            1, 1, 2, 2, 2,    1,    1, 2, 2, 1, 1,    1,    1, 0,
            1, 1, 2, 2, 2,    2,    1, 2, 1, 2, 1,    1,    1, 0,
            1, 2, 1, 1, 1,    1,    2, 1, 1, 1, 2,    1,    2, 0,
            1, 2, 1, 1, 1,    2,    1, 2, 1, 1, 2,    1,    1, 0,
            1, 2, 1, 1, 2,    1,    1, 2, 2, 2, 1,    1,    1, 0,
            1, 2, 1, 1, 2,    2,    1, 2, 2, 1, 1,    1,    1, 0,
            1, 2, 1, 2, 1,    1,    2, 1, 1, 1, 1,    2,    2, 0,
            1, 2, 1, 2, 1,    2,    1, 2, 1, 2, 2,    1,    1, 0,
            1, 2, 1, 2, 2,    1,    1, 1, 2, 1, 1,    1,    1, 0,
            1, 2, 1, 2, 2,    2,    1, 1, 2, 2, 1,    1,    1, 0,
            1, 2, 2, 1, 1,    1,    2, 1, 1, 1, 2,    1,    2, 0,
            1, 2, 2, 1, 1,    2,    1, 2, 2, 1, 2,    1,    1, 0,
            1, 2, 2, 1, 2,    1,    1, 1, 2, 2, 1,    1,    1, 0,
            1, 2, 2, 1, 2,    2,    1, 2, 1, 1, 1,    1,    1, 0,
            1, 2, 2, 2, 1,    1,    2, 1, 1, 1, 2,    1,    2, 0,
            1, 2, 2, 2, 1,    2,    1, 2, 2, 2, 2,    1,    1, 0,
            1, 2, 2, 2, 2,    1,    1, 2, 1, 1, 1,    1,    1, 0,
            1, 2, 2, 2, 2,    2,    1, 1, 2, 1, 1,    1,    1, 0,
            
            2, 1, 1, 1, 1,    1,    2, 1, 1, 1, 1,    1,    1, 0,

            5, 1
        };

    } else if (MACHINE == "wolfram") {
        // Wolfram's 2-state 3-symbol Turing machine
        state_change = {
            {1, 0, 0},
            {0, 1, 0},
        };
        overwrite = {
            {1, 2, 1},
            {2, 2, 0},
        };
        shift = {
            { 1, -1, -1},
            {-1,  1,  1},
        };
        initial_state = 0;
        accepting_state = 2;
        initial_pos = STEPS / 2;
        for (int i = 0; i < STEPS * 2 + 2; i++) {
            initial_tape.emplace_back((int)get_rand_range(0, 2));
        }

    } else {
        print_usage();
        return 1;
    }


    // Conversion to a generalized shift map
    const int n_states = shift.size();
    const int n_symbols = shift[0].size();
    const int n_digits = (int)std::ceil(std::log2(std::max(n_states, n_symbols)));
    GeneralizedShiftMap map(
        [shift](std::vector<bool> v, int pt){return f(shift, v, pt);},
        [state_change, overwrite, shift](std::vector<bool> v, int pt){return g(state_change, overwrite, shift, v, pt);},
        initial_vector(n_digits, initial_state, initial_tape, initial_pos),
        initial_pos * n_digits
    );
    

    // Application of the map
    try {
        for(int i = 0; i < STEPS; i++) {
            // Confirming that the point is in range
            int pt = map.get_point();
            if (pt - n_digits < 0 || map.get_size() <= pt + n_digits * 2) {
                throw std::out_of_range("pointer: " + std::to_string(pt));
            }

            // Application
            map.next();
            map.print_vector();

            // Confirming that the machine is not in halting state
            int current_state = vector_to_num(map.get_subsequence(0, n_digits));
            if (current_state == accepting_state) {
                throw std::runtime_error("machine halted");
            }
        }
    }
    catch (const std::exception& e) {
        std::cout << e.what() << std::endl;
    }


    for(int x: decode(n_digits, map.get_vector())) {
        std::cout << x << ", ";
    }
    std::cout << std::endl;

    return 0;
}
