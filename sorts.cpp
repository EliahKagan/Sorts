#include <iostream>
#include <iterator>
#include <vector>

namespace {
    template<typename C>
    void print(const C& c)
    {
        std::cout << '[';

        auto sep = "";
        for (const auto& x : c) {
            std::cout << sep << x;
            sep = ", ";
        }

        std::cout << "]\n";
    }

    template<typename It>
    void insertion_sort(const It first, const It last)
    {
        if (first == last) return;

        for (auto right = std::next(first); right != last; ++right) {
            auto elem = std::move(*right);

            auto left = right;
            for (; left != first && elem < *std::prev(left); --left)
                *left = *std::prev(left);

            *left = std::move(elem);
        }
    }

    template<typename It>
    void bubble_sort(const It first, const It last)
    {
        if (first == last) return;

        using std::iter_swap;

        for (auto again = true; again; ) {
            again = false;

            for (auto left = first, right = std::next(left); right != last;
                                                             ++left, ++right) {
                if (*right < *left) {
                    using std::iter_swap;
                    iter_swap(left, right);
                    again = true;
                }
            }
        }
    }
}

int main()
{
    std::vector<std::vector<int>> vs {
        {3, 7, 1, 5, 2, -6, 15, 4, 33, -5},
        {9, 9, 1, 8, 3, 0, 2, 0, 7, 15, 4, 3, 3},
        {2, 1},
        {1, 2},
        {5},
        {}
    };

    for (const auto& v : vs) {
        auto v1 = v;
        insertion_sort(begin(v1), end(v1));
        print(v1);

        auto v2 = v;
        bubble_sort(begin(v2), end(v2));
        print(v2);

        std::cout << '\n';
    }
}
