#include <algorithm>
#include <cstddef>
#include <iostream>
#include <iterator>
#include <stack>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <vector>

namespace {
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

        for (auto again = true; again; ) {
            again = false;

            for (auto left = first, right = std::next(left); right != last;
                                                             ++left, ++right) {
                if (*right < *left) {
                    std::iter_swap(left, right);
                    again = true;
                }
            }
        }
    }

    namespace detail {
        template<typename It>
        auto
        make_aux(const typename std::iterator_traits<It>::difference_type len)
        {
            using T = typename std::iterator_traits<It>::value_type;

            std::vector<T> aux;
            aux.reserve(static_cast<typename std::vector<T>::size_type>(len));
            return aux;
        }

        template<typename T, typename It>
        void merge(std::vector<T>& aux, const It first1, // "last1" is first2
                                        const It first2, const It last2)
        {
            auto cur1 = first1, cur2 = first2;

            // Merge elements from both ranges to aux until one is empty.
            while (cur1 != first2 && cur2 != last2) {
                auto& cur = (*cur2 < *cur1 ? cur2 : cur1);
                aux.push_back(std::move(*cur));
                ++cur;
            }

            // Move the remaining elements from whicever range has them.
            std::move(cur1, first2, back_inserter(aux));
            std::move(cur2, last2, back_inserter(aux));

            // Move everything back.
            std::move(cbegin(aux), cend(aux), first1);
            aux.clear();
        }
    }

    template<typename It>
    void mergesort(const It first, const It last)
    {
        auto aux = detail::make_aux<It>(std::distance(first, last));

        const auto mergesort_subrange = [&aux](const auto& me, const It first1,
                                                               const It last2) {
            const auto delta = std::distance(first1, last2) / 2;
            if (delta == 0) return;

            const auto first2 = first1 + delta;
            me(me, first1, first2);
            me(me, first2, last2);
            detail::merge(aux, first1, first2, last2);
        };

        mergesort_subrange(mergesort_subrange, first, last);
    }

    template<typename It>
    void mergesort_iterative(const It first, const It last)
    {
        using Delta = typename std::iterator_traits<It>::difference_type;

        const auto len = std::distance(first, last);
        auto aux = detail::make_aux<It>(len);

        for (Delta delta1 {1}; delta1 < len; delta1 *= 2) {
            Delta sublen {0};

            for (auto first1 = first; (sublen += delta1) < len; ) {
                const auto first2 = std::next(first1, delta1);
                const auto delta2 = std::min(delta1, len - sublen);
                const auto last2 = std::next(first2, delta2);

                detail::merge(aux, first1, first2, last2);

                first1 = last2;
                sublen += delta2;
            }
        }
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
            std::iter_swap(first, first + len);
            sift_down(0);
        }
    }

    template<typename It>
    void quicksort(const It first, const It last) // c.f K&R 2 impl. (p. 87)
    {
        const auto len = std::distance(first, last);
        if (len < 2) return;

        std::iter_swap(first, first + len / 2);
        const auto& pivot = *first;
        auto mid = first;

        for (auto cur = std::next(first); cur != last; ++cur)
            if (*cur < pivot) std::iter_swap(++mid, cur);

        std::iter_swap(first, mid);
        quicksort(first, mid);
        quicksort(std::next(mid), last);
    }

    template<typename It>
    void quicksort_iterative(It first, It last)
    {
        std::stack<std::tuple<It, It>> intervals;
        intervals.emplace(first, last);

        while (!empty(intervals)) {
            std::tie(first, last) = intervals.top();
            intervals.pop();

            const auto len = std::distance(first, last);
            if (len < 2) continue;

            std::iter_swap(first, first + len / 2);
            const auto& pivot = *first;
            auto mid = first;

            for (auto cur = std::next(first); cur != last; ++cur)
                if (*cur < pivot) std::iter_swap(++mid, cur);

            std::iter_swap(first, mid);
            intervals.emplace(std::next(mid), last);
            intervals.emplace(first, mid);
        }
    }

    template<typename>
    struct Label { };

    template<typename F>
    inline constexpr auto label_v = Label<const F>::value;

    inline constexpr auto insertion_sort_f = [](const auto first,
                                                const auto last) {
        insertion_sort(first, last);
    };

    template<>
    struct Label<decltype(insertion_sort_f)> {
        static constexpr std::string_view value {"Insertion sort"};
    };

    inline constexpr auto bubble_sort_f = [](const auto first,
                                             const auto last) {
        bubble_sort(first, last);
    };

    template<>
    struct Label<decltype(bubble_sort_f)> {
        static constexpr std::string_view value {"Bubble sort"};
    };

    inline constexpr auto mergesort_f = [](const auto first, const auto last) {
        mergesort(first, last);
    };

    template<>
    struct Label<decltype(mergesort_f)> {
        static constexpr std::string_view value {
                "Mergesort (top-down, recursive"};
    };

    inline constexpr auto mergesort_iterative_f = [](const auto first,
                                                     const auto last) {
        mergesort_iterative(first, last);
    };

    template<>
    struct Label<decltype(mergesort_iterative_f)> {
        static constexpr std::string_view value {
                "Mergesort (bottom-up, iterative)"};
    };

    inline constexpr auto heapsort_f = [](const auto first, const auto last) {
        heapsort(first, last);
    };

    template<>
    struct Label<decltype(heapsort_f)> {
        static constexpr std::string_view value {"heapsort"};
    };

    inline constexpr auto quicksort_f = [](const auto first, const auto last) {
        quicksort(first, last);
    };

    template<>
    struct Label<decltype(quicksort_f)> {
        static constexpr std::string_view value {"quicksort (recursive)"};
    };

    inline constexpr auto quicksort_iterative_f = [](const auto first,
                                                     const auto last) {
        quicksort_iterative(first, last);
    };

    template<>
    struct Label<decltype(quicksort_iterative_f)> {
        static constexpr std::string_view value {"quicksort (iterative)"};
    };

    template<typename C>
    void print(const C& c, const std::string_view prefix = " ")
    {
        std::cout << prefix << '[';

        auto sep = "";
        for (const auto& x : c) {
            std::cout << sep << x;
            sep = ", ";
        }

        std::cout << ']';
    }

    template<typename C>
    void print_if_small(const C& c, const std::string_view prefix = " ")
    {
        static constexpr std::size_t print_threshold {20};

        if (size(c) <= print_threshold) print(c, prefix);
    }

    template<typename C, typename F>
    void test_one(C c, const F f)
    {
        std::cout << label_v<F> << ':' << std::flush;

        using std::begin, std::end, std::cbegin, std::cend;
        f(begin(c), end(c));

        print_if_small(c);

        const auto ok = std::is_sorted(cbegin(c), cend(c));
        std::cout << ' ' << (ok ? "OK." : "FAIL!!!") << '\n';
    }

    template<typename C, typename... Fs>
    void test(const C& c, const Fs... fs)
    {
        (..., test_one(c, fs));
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
        std::cout << size(v) << "-element vector";
        print_if_small(v);
        std::cout << ".\n";

        test(v, insertion_sort_f,
                bubble_sort_f,
                mergesort_f,
                mergesort_iterative_f,
                heapsort_f,
                quicksort_f,
                quicksort_iterative_f);

        std::cout << '\n';
    }
}
