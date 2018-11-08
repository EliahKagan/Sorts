#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <iostream>
#include <iterator>
#include <limits>
#include <random>
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
                *left = std::move(*std::prev(left));

            *left = std::move(elem);
        }
    }

    template<typename It>
    void selection_sort(It first, const It last)
    {
        for (; first != last; ++first)
            std::iter_swap(std::min_element(first, last), first);
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
        // Generates the Tokuda gap sequence. See https://oeis.org/A108870 and
        // formulas at https://en.wikipedia.org/wiki/Shellsort#Gap_sequences.
        template<typename D>
        std::vector<D> tokuda_gaps(const D len)
        {
            static_assert(std::is_integral_v<D> && std::is_signed_v<D>);

            std::vector<D> gaps;

            for (auto h = 1.0; ; h = h * 2.25 + 1.0) {
                const auto g = static_cast<D>(std::ceil(h));
                if (g >= len) break;
                gaps.push_back(g);
            }

            assert(empty(gaps) || gaps.front() == 1);
            return gaps;
        }

        template<typename It>
        void gapped_insertion_sort(It first, const It last,
                                   const typename It::difference_type gap)
        {
            for (auto len = last - first; gap < len; ++first, --len) {
                for (auto right = gap; right < len; right += gap) {
                    auto elem = std::move(first[right]);

                    auto left = right;
                    for (; left != 0 && elem < first[left - gap]; left -= gap)
                        first[left] = std::move(first[left - gap]);

                    first[left] = std::move(elem);
                }
            }
        }
    }

    template<typename It>
    void shellsort_tokuda(const It first, const It last)
    {
        const auto gaps = detail::tokuda_gaps(std::distance(first, last));

        std::for_each(std::crbegin(gaps), std::crend(gaps),
                      [first, last](const typename It::difference_type gap) {
            detail::gapped_insertion_sort(first, last, gap);
        });
    }

    namespace detail {
        template<typename It>
        constexpr bool possibly_unsorted(It first, const It last) noexcept
        {
            return first != last && ++first != last;
        }

        template<typename It>
        constexpr It midpoint(It first, const It last) noexcept
        {
            std::advance(first, std::distance(first, last) / 2);
            return first;
        }

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

            // Move the remaining elements from whichever range has them.
            std::move(cur1, first2, back_inserter(aux));
            std::move(cur2, last2, back_inserter(aux));

            // Move everything back.
            std::move(cbegin(aux), cend(aux), first1);
            aux.clear();
        }
    }

    template<typename It>
    void mergesort_topdown(const It first, const It last)
    {
        auto aux = detail::make_aux<It>(std::distance(first, last));

        const auto mergesort_subrange = [&aux](const auto& me, const It first1,
                                                               const It last2) {
            const auto delta = std::distance(first1, last2) / 2;
            if (delta == 0) return;

            const auto first2 = std::next(first1, delta);
            me(me, first1, first2);
            me(me, first2, last2);
            detail::merge(aux, first1, first2, last2);
        };

        mergesort_subrange(mergesort_subrange, first, last);
    }

    template<typename It>
    void mergesort_topdown_iterative(It first, It last)
    {
        auto aux = detail::make_aux<It>(std::distance(first, last));
        auto post_first = last, post_last = last; // a "null" interval
        std::stack<std::tuple<It, It>> intervals;

        while (first != last || !empty(intervals)) {
            // Traverse left as far as possible.
            for (; first != last; last = detail::midpoint(first, last))
                intervals.emplace(first, last);

            const auto [first1, last2] = intervals.top();

            if (const auto first2 = detail::midpoint(first1, last2);
                    // The right branch is big enough to need sorting...
                    detail::possibly_unsorted(first2, last2)
                    // ...and we were not just there.
                        && (first2 != post_first || last2 != post_last)) {
                // Traverse there next.
                first = first2;
                last = last2;
            } else {
                // Merge the left and right branches and retreat.
                detail::merge(aux, first1, first2, last2);
                post_first = first1;
                post_last = last2;
                intervals.pop();
            }
        }
    }

    template<typename It>
    void mergesort_bottomup_iterative(const It first, const It last)
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

    namespace detail {
        // Assumes [first, last) is nonempty, partitions it, and returns an
        // iterator to the pivot. Like the Lomuto scheme, but chooses the pivot
        // from the middle, not the end. This is the K&R 2 algorithm (p. 87).
        template<typename It>
        It partition_lomuto(const It first, const It last)
        {
            std::iter_swap(first, midpoint(first, last));
            const auto& pivot = *first;
            auto mid = first;

            for (auto cur = std::next(first); cur != last; ++cur)
                if (*cur < pivot) std::iter_swap(++mid, cur);

            std::iter_swap(first, mid);
            return mid;
        }
    }

    template<typename It>
    void quicksort_lomuto(const It first, const It last)
    {
        if (detail::possibly_unsorted(first, last)) {
            auto mid = detail::partition_lomuto(first, last);
            quicksort_lomuto(first, mid);
            quicksort_lomuto(++mid, last);
        }
    }

    template<typename It>
    void quicksort_lomuto_iterative(It first, It last)
    {
        std::stack<std::tuple<It, It>> intervals;
        intervals.emplace(first, last);

        while (!empty(intervals)) {
            std::tie(first, last) = intervals.top();
            intervals.pop();

            if (!detail::possibly_unsorted(first, last)) continue;

            const auto mid = detail::partition_lomuto(first, last);
            intervals.emplace(std::next(mid), last);
            intervals.emplace(first, mid);
        }
    }

    template<typename It>
    void stdlib_heapsort(const It first, const It last)
    {
        std::make_heap(first, last);
        std::sort_heap(first, last);
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

    inline constexpr auto selection_sort_f = [](const auto first,
                                                const auto last) {
        selection_sort(first, last);
    };

    template<>
    struct Label<decltype(selection_sort_f)> {
        static constexpr std::string_view value {"Selection sort"};
    };

    inline constexpr auto bubble_sort_f = [](const auto first,
                                             const auto last) {
        bubble_sort(first, last);
    };

    template<>
    struct Label<decltype(bubble_sort_f)> {
        static constexpr std::string_view value {"Bubble sort"};
    };

    inline constexpr auto shellsort_tokuda_f = [](const auto first,
                                                  const auto last) {
        shellsort_tokuda(first, last);
    };

    template<>
    struct Label<decltype(shellsort_tokuda_f)> {
        static constexpr std::string_view value {
                "Shellsort (Tokuda gap sequence)"};
    };

    inline constexpr auto mergesort_topdown_f = [](const auto first,
                                                   const auto last) {
        mergesort_topdown(first, last);
    };

    template<>
    struct Label<decltype(mergesort_topdown_f)> {
        static constexpr std::string_view value {
                "Mergesort (top-down, recursive)"};
    };

    inline constexpr auto mergesort_topdown_iterative_f = [](const auto first,
                                                             const auto last) {
        mergesort_topdown_iterative(first, last);
    };

    template<>
    struct Label<decltype(mergesort_topdown_iterative_f)> {
        static constexpr std::string_view value {
            "Mergesort (top-down, iterative)"};
    };

    inline constexpr auto mergesort_bottomup_iterative_f = [](const auto first,
                                                              const auto last) {
        mergesort_bottomup_iterative(first, last);
    };

    template<>
    struct Label<decltype(mergesort_bottomup_iterative_f)> {
        static constexpr std::string_view value {
                "Mergesort (bottom-up, iterative)"};
    };

    inline constexpr auto heapsort_f = [](const auto first, const auto last) {
        heapsort(first, last);
    };

    template<>
    struct Label<decltype(heapsort_f)> {
        static constexpr std::string_view value {"Heapsort"};
    };

    inline constexpr auto quicksort_lomuto_f = [](const auto first,
                                                  const auto last) {
        quicksort_lomuto(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_f)> {
        static constexpr std::string_view value {
                "Quicksort (Lomuto partitioning, recursive)"};
    };

    inline constexpr auto quicksort_lomuto_iterative_f = [](const auto first,
                                                            const auto last) {
        quicksort_lomuto_iterative(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_iterative_f)> {
        static constexpr std::string_view value {
                "Quicksort (Lomuto partitioning, iterative)"};
    };

    inline constexpr auto stdlib_heapsort_f = [](const auto first,
                                                 const auto last) {
        stdlib_heapsort(first, last);
    };

    template<>
    struct Label<decltype(stdlib_heapsort_f)> {
        static constexpr std::string_view value {
            "std::make_heap + std::sort_heap (heapsort)"};
    };

    inline constexpr auto stdlib_mergesort_f = [](const auto first,
                                                  const auto last) {
        std::stable_sort(first, last);
    };

    template<>
    struct Label<decltype(stdlib_mergesort_f)> {
        static constexpr std::string_view value {
                "std::stable_sort (usually adaptive mergesort)"};
    };

    inline constexpr auto stdlib_introsort_f = [](const auto first,
                                                  const auto last) {
        std::sort(first, last);
    };

    template<>
    struct Label<decltype(stdlib_introsort_f)> {
        static constexpr std::string_view value {
                "std::sort (usually introsort)"};
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
        using namespace std::chrono;
        using std::begin, std::end, std::cbegin, std::cend;

        std::cout << label_v<F> << ':' << std::flush;

        const auto ti = steady_clock::now();
        f(begin(c), end(c));
        const auto tf = steady_clock::now();

        const auto dt = duration_cast<milliseconds>(tf - ti);
        std::cout << ' ' << dt.count() << "ms";

        print_if_small(c);

        const auto ok = std::is_sorted(cbegin(c), cend(c));
        std::cout << ' ' << (ok ? "OK." : "FAIL!!!") << '\n';
    }

    template<typename C, typename... Fs>
    void test_algorithms(const C& c, const Fs... fs)
    {
        (..., test_one(c, fs));
    }

    template<typename C>
    void test_slow(const C& c)
    {
        test_algorithms(c, insertion_sort_f,
                           selection_sort_f,
                           bubble_sort_f);
    }

    template<typename C>
    void test_fast(const C& c)
    {
        test_algorithms(c, shellsort_tokuda_f,
                           mergesort_topdown_f,
                           mergesort_topdown_iterative_f,
                           mergesort_bottomup_iterative_f,
                           heapsort_f,
                           quicksort_lomuto_f,
                           quicksort_lomuto_iterative_f,
                           stdlib_heapsort_f,
                           stdlib_mergesort_f,
                           stdlib_introsort_f);
    }
}

int main()
{
    using Range = std::numeric_limits<int>;
    using Dist = std::uniform_int_distribution<int>;

    auto generate = [eng = std::mt19937{std::random_device{}()},
                     dist = Dist{Range::min(), Range::max()}
            ](const std::size_t len) mutable {
        std::vector<int> a (len);
        for (auto& x : a) x = dist(eng);
        return a;
    };

    const std::vector<std::vector<int>> vs {
        {111, 333, 222},
        {3, 7, 1, 5, 2, -6, 15, 4, 33, -5},
        {9, 9, 1, 8, 3, 0, 2, 0, 7, 15, 4, 3, 3},
        {2, 1},
        {1, 2},
        {5},
        {},
        generate(6),
        generate(1000),
        generate(10'000),
        generate(100'000),
        generate(1'000'000),
        generate(10'000'000),
        generate(100'000'000),
        //generate(1'000'000'000)
    };

    for (const auto& v : vs) {
        std::cout << size(v) << "-element vector";
        print_if_small(v);
        std::cout << ".\n";

        if (size(v) <= 100'000) test_slow(v);
        test_fast(v);

        std::cout << '\n';
    }
}
