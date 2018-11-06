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

    for (auto& v : vs) {
        insertion_sort(begin(v), end(v));
        print(v);
    }
}
