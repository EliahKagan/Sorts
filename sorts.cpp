#include <algorithm>
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

    template<typename It>
    void mergesort(const It first, const It last)
    {
        using T = typename std::iterator_traits<It>::value_type;

        const auto len = std::distance(first, last);
        std::vector<T> aux;
        aux.reserve(static_cast<typename std::vector<T>::size_type>(len));

        const auto merge = [&aux](const It first1, // "last1" is first2
                                  const It first2, const It last2) {
            auto cur1 = first1, cur2 = first2;

            // merge elements from both ranges to aux until one is empty
            while (cur1 != first2 && cur2 != last2) {
                auto& cur = (*cur2 < *cur1 ? cur2 : cur1);
                aux.push_back(std::move(*cur));
                ++cur;
            }

            // move the remaining elements from whicever range has them
            std::move(cur1, first2, std::back_inserter(aux));
            std::move(cur2, last2, std::back_inserter(aux));

            // move everything back
            std::move(cbegin(aux), cend(aux), first1);
            aux.clear();
        };

        const auto mergesort_subrange = [merge](const auto& me, const It first1,
                                                                const It last2) {
            const auto sublen = std::distance(first1, last2);
            if (sublen < 2) return;

            const auto first2 = first1 + sublen / 2;
            me(me, first1, first2);
            me(me, first2, last2);
            merge(first1, first2, last2);
        };

        mergesort_subrange(mergesort_subrange, first, last);
    }

    template<typename It>
    void heapsort(const It first, const It last)
    {
        auto len = last - first;
        if (len < 2) return;

        static constexpr decltype(len) no_child {-1};

        const auto pick_child = [first, &len](const decltype(len) parent) {
            const auto left = parent * 2 + 1;
            if (left >= len) return no_child;

            const auto right = left + 1;
            return right == len || !(first[left] < first[right]) ? left : right;
        };

        const auto sift_down = [first, pick_child](decltype(len) parent) {
            auto elem = std::move(first[parent]);

            for (; ; ) {
                const auto child = pick_child(parent);
                if (child == no_child || !(elem < first[child])) break;

                first[parent] = std::move(first[child]);
                parent = child;
            }

            first[parent] = std::move(elem);
        };

        // Rearrange the elements into a binary maxheap.
        for (auto parent = len / 2; parent >= 0; --parent) sift_down(parent);

        // Pop each maximum element and place it just after the unsorted region.
        while (--len != 0) {
            using std::iter_swap;
            iter_swap(first, first + len);
            sift_down(0);
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

        auto v3 = v;
        mergesort(begin(v3), end(v3));
        print(v3);

        auto v4 = v;
        heapsort(begin(v4), end(v4));
        print(v4);

        std::cout << '\n';
    }
}
