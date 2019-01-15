#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <limits>
#include <memory>
#include <random>
#include <stack>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
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
    void insertion_sort_byswap(const It first, const It last)
    {
        if (first == last) return;

        for (auto right = std::next(first); right != last; ++right) {
            for (auto left = right; left != first && *left < *std::prev(left);
                                    --left)
                std::iter_swap(left, std::prev(left));
        }
    }

    template<typename It>
    void binary_insertion_sort(const It first, const It last)
    {
        if (first == last) return;

        for (auto right = std::next(first); right != last; ++right) {
            auto elem = std::move(*right);

            const auto left = std::upper_bound(first, right, elem);
            std::move_backward(left, right, std::next(right));

            *left = std::move(elem);
        }
    }

    template<typename It>
    void binary_insertion_sort_byrotate(const It first, const It last)
    {
        if (first == last) return;

        for (auto right = std::next(first); right != last; ++right) {
            const auto left = std::upper_bound(first, right, *right);
            std::rotate(left, right, std::next(right));
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

    template<typename It>
    void bubble_sort_nonadaptive(const It first, It last)
    {
        for (; first != last; --last) {
            for (auto left = first, right = std::next(left); right != last;
                                                             ++left, ++right) {
                if (*right < *left) std::iter_swap(left, right);
            }
        }
    }

    template<typename It>
    void bubble_sort_maxadaptive(const It first, It last)
    {
        while (first != last) {
            auto last_swapped = first;

            for (auto left = first, right = std::next(left); right != last;
                                                             ++left, ++right) {
                if (*right < *left) {
                    std::iter_swap(left, right);
                    last_swapped = right;
                }
            }

            last = last_swapped;
        }
    }

    template<typename It>
    void gnome_sort(const It first, const It last)
    {
        for (auto cur = first; cur != last; ) {
            if (cur == first || !(*cur < *std::prev(cur))) {
                ++cur;
            } else {
                std::iter_swap(cur, std::prev(cur));
                --cur;
            }
        }
    }

    namespace detail {
        template<typename It>
        using Delta = typename std::iterator_traits<It>::difference_type;

        template<typename It>
        void insertion_sort_subsequence(const It first, const It last,
                                        const Delta<It> gap)
        {
            const auto len = last - first;

            for (auto right = gap; right < len; right += gap) {
                auto elem = std::move(first[right]);

                auto left = right;
                for (; left != 0 && elem < first[left - gap]; left -= gap)
                    first[left] = std::move(first[left - gap]);

                first[left] = std::move(elem);
            }
        }

        template<typename It, typename Gen>
        void shellsort(const It first, const It last, const Gen generate_gaps)
        {
            // Get the gap sequence.
            std::vector<Delta<It>> gaps;
            generate_gaps(last - first, std::back_inserter(gaps));
            assert(empty(gaps) || gaps.front() == 1);

            // Do all nonoverlapping gapped insertion sorts for each gap value.
            std::for_each(std::crbegin(gaps), std::crend(gaps),
                          [first, last](const Delta<It> gap) {
                const auto bound = first + gap;

                for (auto start = first; start != bound; ++start)
                    insertion_sort_subsequence(start, last, gap);
            });
        }

        // This ratio appears in the computations of some of the experimentally
        // faster (average-case) gap sequences for shellsort.
        inline constexpr auto nine_fourths = 2.25;

        // This is the fastest known sequence in the average case, based on
        // experimental evidence. Only nine terms are known (with no formula).
        inline constexpr std::array ciura_gaps = {
                1, 4, 10, 23, 57, 132, 301, 701, 1750};
    }

    namespace detail::gaps {
        // Generates gaps consisting of one less than powers of 2. Found by
        // Hibbard 1963: https://dl.acm.org/citation.cfm?doid=366552.366557
        inline constexpr auto hibbard = [](const auto len, auto d_first) {
            for (auto k = 1; ; ++k) {
                const auto g = (decltype(len){1} << k) - 1;
                if (g >= len) break;
                *d_first++ = g;
            }
        };

        // Generates gaps consisting of the 3-smooth numbers. Pratt 1971 showed
        // shellsort with this sequence has optimal worst-case asymptotic time
        // complexity, http://www.dtic.mil/get-tr-doc/pdf?AD=AD0740110, but on
        // average it is slower than the popular sequences. I generate them with
        // David Eisenstat's method https://stackoverflow.com/a/25344494
        // (Eisenstat 2014) based on Dijkstra's solution to the Hamming problem
        // (Dijkstra 1976, see https://en.wikipedia.org/wiki/Regular_number).
        inline constexpr auto three_smooth = [](const auto len, auto d_first) {
            std::vector<std::remove_const_t<decltype(len)>> aux;
            decltype(size(aux)) co_two_pos {}, co_three_pos {};

            for (aux.push_back({1}); aux.back() < len; ) {
                *d_first++ = aux.back();

                const auto two_multiple = aux[co_two_pos] * 2;
                const auto three_multiple = aux[co_three_pos] * 3;

                aux.push_back(std::min(two_multiple, three_multiple));

                if (two_multiple <= three_multiple) ++co_two_pos;
                if (three_multiple <= two_multiple) ++co_three_pos;
            }
        };

        // Generate gaps whose rate of increase gradually rises. Found by
        // Sedgewick 1986: https://doi.org/10.1016/0196-6774(86)90001-5 p.165
        // See also https://oeis.org/A036562.
        inline constexpr auto sedgewick = [](const auto len, auto d_first) {
            if (len == 0) return;

            constexpr decltype(len) one {1};
            *d_first++ = one;

            for (auto i = 0; ; ++i) {
                const auto g = (one << (i + 1) * 2) + (one << i) * 3 + 1;
                if (g >= len) break;
                *d_first++ = g;
            }
        };

        // Generates gaps that increase by a bit more than 9/4. Found by
        // Tokuda 1992: https://dl.acm.org/citation.cfm?id=659879. See also
        // https://oeis.org/A108870. The formula used here appears in
        // https://en.wikipedia.org/wiki/Shellsort#Gap_sequences.
        inline constexpr auto tokuda = [](const auto len, auto d_first) {
            for (auto h = 1.0; ; h = h * nine_fourths + 1.0) {
                const auto g = static_cast<decltype(len)>(std::ceil(h));
                if (g >= len) break;
                *d_first++ = g;
            }
        };

        // Generates gaps that increase according to the short experimentally
        // derived sequence in Ciura 2001, and then by a bit less than 9/4. See
        // http://sun.aei.polsl.pl/~mciura/publikacje/shellsort.pdf and
        // https://oeis.org/A102549 for the initial sequence and
        // https://en.wikipedia.org/wiki/Shellsort#Gap_sequences for the
        // idea of extending it in this way.
        inline constexpr auto quasi_ciura = [](const auto len, auto d_first) {
            auto g = decltype(len){};

            for (const auto h : ciura_gaps) {
                g = decltype(len){h};
                if (g >= len) return;
                *d_first++ = g;
            }

            while ((g = static_cast<decltype(len)>(g * nine_fourths)) < len)
                *d_first++ = g;
        };
    }

    template<typename It>
    void shellsort_hibbard(const It first, const It last)
    {
        detail::shellsort(first, last, detail::gaps::hibbard);
    }

    template<typename It>
    void shellsort_3smooth(const It first, const It last)
    {
        detail::shellsort(first, last, detail::gaps::three_smooth);
    }

    template<typename It>
    void shellsort_sedgewick(const It first, const It last)
    {
        detail::shellsort(first, last, detail::gaps::sedgewick);
    }

    template<typename It>
    void shellsort_tokuda(const It first, const It last)
    {
        detail::shellsort(first, last, detail::gaps::tokuda);
    }

    template<typename It>
    void shellsort_quasi_ciura(const It first, const It last)
    {
        detail::shellsort(first, last, detail::gaps::quasi_ciura);
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
        make_aux(const Delta<It> len)
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
        const auto len = std::distance(first, last);
        auto aux = detail::make_aux<It>(len);

        for (detail::Delta<It> delta1 {1}; delta1 < len; delta1 *= 2) {
            detail::Delta<It> sublen {0};

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

    namespace detail {
        template<typename It>
        inline constexpr Delta<It> no_child {-1};

        template<typename It>
        constexpr Delta<It> pick_child(const It first, const Delta<It> len,
                                       const Delta<It> parent)
        {
            const auto left = parent * 2 + 1;
            if (left >= len) return no_child<It>;

            const auto right = left + 1;
            return right == len || !(first[left] < first[right]) ? left : right;
        }
    }

    template<typename It>
    void heapsort(const It first, const It last)
    {
        auto len = last - first;
        if (len < 2) return;

        const auto sift_down = [first, &len](detail::Delta<It> parent) {
            auto elem = std::move(first[parent]);

            for (; ; ) {
                const auto child = detail::pick_child(first, len, parent);
                if (child == detail::no_child<It> || !(elem < first[child]))
                    break;

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
    void heapsort_byswap(const It first, const It last)
    {
        auto len = last - first;
        if (len < 2) return;

        const auto sift_down = [first, &len](detail::Delta<It> parent) {
            for (; ; ) {
                const auto child = detail::pick_child(first, len, parent);
                if (child == detail::no_child<It>
                        || !(first[parent] < first[child]))
                    break;

                std::iter_swap(first + parent, first + child);
                parent = child;
            }
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
        template<typename It>
        constexpr void bring_mid_to_front(const It first, const It last)
        {
            std::iter_swap(first, midpoint(first, last));
        }

        template<typename It>
        constexpr It iter_min(const It p, const It q)
        {
            return *q < *p ? q : p;
        }

        template<typename It>
        constexpr It median_of_three(const It p, const It q, const It r)
        {
            if (*p < *q)
                return *p < *r ? iter_min(q, r) : p;
            else
                return *q < *r ? iter_min(p, r) : q;
        }

        template<typename It>
        constexpr void bring_median_of_three_to_front(const It first,
                                                      const It last)
        {
            std::iter_swap(first, median_of_three(first,
                                                  midpoint(first, last),
                                                  last - 1));
        }

        // Sorts in the simple cases of two or fewer elements and returns true,
        // or moves the median-of-three element to the front and returns false.
        template<typename It>
        constexpr bool sorted_after_pivot_selection(const It first, It last)
        {
            if (const auto len = last - first; len < 3) {
                if (len == 2 && *--last < *first) std::iter_swap(first, last);
                return true;
            }

            bring_median_of_three_to_front(first, last);
            return false;
        }
    }

    namespace detail::partitions {
        // Assumes [first, last) is nonempty, partitions it, and returns an
        // iterator to the pivot. Like the Lomuto scheme, but chooses the pivot
        // from the beginning, not the end.
        template<typename It>
        It lomuto(const It first, const It last)
        {
            const auto& pivot = *first;
            auto mid = first;

            for (auto cur = std::next(first); cur != last; ++cur)
                if (*cur < pivot) std::iter_swap(++mid, cur);

            std::iter_swap(first, mid);
            return mid;
        }

        // Hoare partition scheme. This implementation assumes the first element
        // in the range is neither the strictly least nor the strictly greatest
        // element.
        template<typename It>
        It hoare(It first, It last)
        {
            for (const auto& pivot = *first; ; ) {
                while (*++first < pivot) { }
                while (pivot < *--last) { }
                if (first >= last) return first;
                std::iter_swap(first, last);
            }
        }
    }

    // Quicksort, using Lomuto partition but choosing the pivot from the middle
    // of the array (by swapping the first and middle elements and then using
    // the first element as the pivot). This is the K&R 2 algorithm (p. 87).
    template<typename It>
    void quicksort_lomuto_simple(const It first, const It last)
    {
        if (detail::possibly_unsorted(first, last)) {
            detail::bring_mid_to_front(first, last);
            auto mid = detail::partitions::lomuto(first, last);
            quicksort_lomuto_simple(first, mid);
            quicksort_lomuto_simple(++mid, last);
        }
    }

    // Same as quicksort_lomuto_simple, but implemented iteratively.
    template<typename It>
    void quicksort_lomuto_simple_iterative(It first, It last)
    {
        std::stack<std::tuple<It, It>> intervals;
        intervals.emplace(first, last);

        while (!empty(intervals)) {
            std::tie(first, last) = intervals.top();
            intervals.pop();

            if (!detail::possibly_unsorted(first, last)) continue;

            detail::bring_mid_to_front(first, last);
            const auto mid = detail::partitions::lomuto(first, last);
            intervals.emplace(std::next(mid), last);
            intervals.emplace(first, mid);
        }
    }

    // Quicksort, using Lomuto partition but choosing the pivot via the median-
    // of-three tecdhnique.
    template<typename It>
    void quicksort_lomuto(const It first, const It last)
    {
        if (detail::sorted_after_pivot_selection(first, last)) return;
        auto mid = detail::partitions::lomuto(first, last);
        quicksort_lomuto(first, mid);
        quicksort_lomuto(++mid, last);
    }

    // Same as quicksort_lomuto, but implemented iteratively.
    template<typename It>
    void quicksort_lomuto_iterative(It first, It last)
    {
        std::stack<std::tuple<It, It>> intervals;
        intervals.emplace(first, last);

        while (!empty(intervals)) {
            std::tie(first, last) = intervals.top();
            intervals.pop();

            if (detail::sorted_after_pivot_selection(first, last)) continue;
            const auto mid = detail::partitions::lomuto(first, last);
            intervals.emplace(mid + 1, last);
            intervals.emplace(first, mid);
        }
    }

    // Quicksort using Hoare partition.
    template<typename It>
    void quicksort_hoare(const It first, const It last)
    {
        if (detail::sorted_after_pivot_selection(first, last)) return;
        auto mid = detail::partitions::hoare(first, last);
        quicksort_hoare(first, mid);
        quicksort_hoare(mid, last);
    }

    // Quicksort using Hoare partition, but implemented iteratively.
    template<typename It>
    void quicksort_hoare_iterative(It first, It last)
    {
        std::stack<std::tuple<It, It>> intervals;
        intervals.emplace(first, last);

        while (!empty(intervals)) {
            std::tie(first, last) = intervals.top();
            intervals.pop();

            if (detail::sorted_after_pivot_selection(first, last)) continue;
            const auto mid = detail::partitions::hoare(first, last);
            intervals.emplace(mid, last);
            intervals.emplace(first, mid);
        }
    }

    template<typename It>
    void stdlib_heapsort(const It first, const It last)
    {
        std::make_heap(first, last);
        std::sort_heap(first, last);
    }

    namespace detail {
        template<typename It>
        using ValueType = typename std::iterator_traits<It>::value_type;

        template<typename It>
        inline constexpr auto accurate_value_type_v = std::is_same_v<
                ValueType<It>,
                std::remove_reference_t<decltype(*std::declval<It>())>>;

        template<typename It>
        using ValueTypeVector = std::vector<ValueType<It>>;

        template<typename It>
        inline constexpr auto known_vector_iterator_v =
            std::is_same_v<It, typename ValueTypeVector<It>::const_iterator>
                || std::is_same_v<It, typename ValueTypeVector<It>::iterator>;

        template<typename It>
        inline constexpr auto known_contiguous_v =
            std::is_pointer_v<It> || known_vector_iterator_v<It>;
    }

    template<typename It>
    void stdlib_qsort(const It first, const It last)
    {
        static_assert(detail::accurate_value_type_v<It>,
                "iterator appears not to report its value type correctly");
        static_assert(detail::known_contiguous_v<It>,
                "iterator type not in the short known-contiguous whitelist");
        static_assert(!std::is_const_v<detail::ValueType<It>>,
                "can't safely sort a range using iterators to const");
        static_assert(std::is_trivial_v<detail::ValueType<It>>,
                "can't safely std::qsort elements not satisfying TrivialType");

        const auto len = last - first;
        assert(len >= 0);
        if (len == 0) return;

        std::qsort(std::addressof(*first), static_cast<std::size_t>(len),
                   sizeof *first, [](const void* const p, const void* const q) {
            const auto& lhs = *static_cast<const detail::ValueType<It>*>(p);
            const auto& rhs = *static_cast<const detail::ValueType<It>*>(q);

            if (lhs < rhs) return -1;
            if (rhs < lhs) return +1;
            return 0;
        });
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

    inline constexpr auto insertion_sort_byswap_f = [](const auto first,
                                                       const auto last) {
        insertion_sort_byswap(first, last);
    };

    template<>
    struct Label<decltype(insertion_sort_byswap_f)> {
        static constexpr std::string_view value {"Insertion sort (swapping)"};
    };

    inline constexpr auto binary_insertion_sort_f = [](const auto first,
                                                       const auto last) {
        binary_insertion_sort(first, last);
    };

    template<>
    struct Label<decltype(binary_insertion_sort_f)> {
        static constexpr std::string_view value {"Binary insertion sort"};
    };

    inline constexpr auto binary_insertion_sort_byrotate_f =
            [](const auto first, const auto last) {
        binary_insertion_sort_byrotate(first, last);
    };

    template<>
    struct Label<decltype(binary_insertion_sort_byrotate_f)> {
        static constexpr std::string_view value {
                "Binary insertion sort (rotating)"};
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
        static constexpr std::string_view value {"Bubble sort (classic)"};
    };

    inline constexpr auto bubble_sort_nonadaptive_f = [](const auto first,
                                                         const auto last) {
        bubble_sort_nonadaptive(first, last);
    };

    template<>
    struct Label<decltype(bubble_sort_nonadaptive_f)> {
        static constexpr std::string_view value {"Bubble sort (non-adaptive)"};
    };

    inline constexpr auto bubble_sort_maxadaptive_f = [](const auto first,
                                                         const auto last) {
        bubble_sort_maxadaptive(first, last);
    };

    template<>
    struct Label<decltype(bubble_sort_maxadaptive_f)> {
        static constexpr std::string_view value {
                "Bubble sort (fully adaptive)"};
    };

    inline constexpr auto gnome_sort_f = [](const auto first,
                                            const auto last) {
        gnome_sort(first, last);
    };

    template<>
    struct Label<decltype(gnome_sort_f)> {
        static constexpr std::string_view value {"Gnome sort"};
    };

    inline constexpr auto shellsort_hibbard_f = [](const auto first,
                                                   const auto last) {
        shellsort_hibbard(first, last);
    };

    template<>
    struct Label<decltype(shellsort_hibbard_f)> {
        static constexpr std::string_view value {
                "Shellsort (Hibbard gap sequence)"};
    };

    inline constexpr auto shellsort_3smooth_f = [](const auto first,
                                                   const auto last) {
        shellsort_3smooth(first, last);
    };

    template<>
    struct Label<decltype(shellsort_3smooth_f)> {
        static constexpr std::string_view value {
                "Shellsort (3-smooth gap sequence)"};
    };

    inline constexpr auto shellsort_sedgewick_f = [](const auto first,
                                                     const auto last) {
        shellsort_sedgewick(first, last);
    };

    template<>
    struct Label<decltype(shellsort_sedgewick_f)> {
        static constexpr std::string_view value {
                "Shellsort (Sedgewick gap sequence)"};
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

    inline constexpr auto shellsort_quasi_ciura_f = [](const auto first,
                                                       const auto last) {
        shellsort_quasi_ciura(first, last);
    };

    template<>
    struct Label<decltype(shellsort_quasi_ciura_f)> {
        static constexpr std::string_view value {
                "Shellsort (Extended Ciura gap sequence)"};
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

    inline constexpr auto heapsort_byswap_f = [](const auto first,
                                                 const auto last) {
        heapsort_byswap(first, last);
    };

    template<>
    struct Label<decltype(heapsort_byswap_f)> {
        static constexpr std::string_view value {"Heapsort (swapping)"};
    };

    inline constexpr auto quicksort_lomuto_simple_f = [](const auto first,
                                                         const auto last) {
        quicksort_lomuto_simple(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_simple_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Lomuto partitioning, middle-element pivot, recursive)"};
    };

    inline constexpr auto quicksort_lomuto_simple_iterative_f =
                            [](const auto first, const auto last) {
        quicksort_lomuto_simple_iterative(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_simple_iterative_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Lomuto partitioning, middle-element pivot, iterative)"};
    };

    inline constexpr auto quicksort_lomuto_f = [](const auto first,
                                                  const auto last) {
        quicksort_lomuto(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Lomuto partitioning, median-of-three pivot, recursive)"};
    };

    inline constexpr auto quicksort_lomuto_iterative_f = [](const auto first,
                                                            const auto last) {
        quicksort_lomuto_iterative(first, last);
    };

    template<>
    struct Label<decltype(quicksort_lomuto_iterative_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Lomuto partitioning, median-of-three pivot, iterative)"};
    };

    inline constexpr auto quicksort_hoare_f = [](const auto first,
                                                 const auto last) {
        quicksort_hoare(first, last);
    };

    template<>
    struct Label<decltype(quicksort_hoare_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Hoare partitioning, median-of-three pivot, recursive)"};
    };

    inline constexpr auto quicksort_hoare_iterative_f = [](const auto first,
                                                           const auto last) {
        quicksort_hoare_iterative(first, last);
    };

    template<>
    struct Label<decltype(quicksort_hoare_iterative_f)> {
        static constexpr std::string_view value {
                "Quicksort "
                "(Hoare partitioning, median-of-three pivot, iterative)"};
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

    inline constexpr auto stdlib_qsort_f = [](const auto first,
                                              const auto last) {
        stdlib_qsort(first, last);
    };

    template<>
    struct Label<decltype(stdlib_qsort_f)> {
        static constexpr std::string_view value {
            "std::qsort (often quicksort)"};
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
    void test_insertion_sorts(const C& c)
    {
        test_algorithms(c, insertion_sort_f,
                           insertion_sort_byswap_f,
                           binary_insertion_sort_f,
                           binary_insertion_sort_byrotate_f);
    }

    template<typename C>
    void test_other_slow(const C& c)
    {
        test_algorithms(c, selection_sort_f,
                           bubble_sort_f,
                           bubble_sort_nonadaptive_f,
                           bubble_sort_maxadaptive_f,
                           gnome_sort_f);
    }

    template<typename C>
    void test_fast(const C& c)
    {
        test_algorithms(c, shellsort_hibbard_f,
                           shellsort_3smooth_f,
                           shellsort_sedgewick_f,
                           shellsort_tokuda_f,
                           shellsort_quasi_ciura_f,
                           mergesort_topdown_f,
                           mergesort_topdown_iterative_f,
                           mergesort_bottomup_iterative_f,
                           heapsort_f,
                           heapsort_byswap_f,
                           quicksort_lomuto_simple_f,
                           quicksort_lomuto_simple_iterative_f,
                           quicksort_lomuto_f,
                           quicksort_lomuto_iterative_f,
                           quicksort_hoare_f,
                           quicksort_hoare_iterative_f,
                           stdlib_heapsort_f,
                           stdlib_mergesort_f,
                           stdlib_introsort_f,
                           stdlib_qsort_f);
    }

    bool will_do_slowest(const int argc, const char* const* const argv)
    {
        assert(argc > 0);

        return std::none_of(argv + 1, argv + argc, [](const auto arg) noexcept {
            using namespace std::string_view_literals;
            return arg == "-S"sv || arg == "--skip-slowest"sv;
        });
    }

    auto make_generator()
    {
        using Range = std::numeric_limits<int>;
        using Dist = std::uniform_int_distribution<int>;

        return [eng = std::mt19937{std::random_device{}()},
                dist = Dist{Range::min(), Range::max()}](const std::size_t len)
                mutable {
            std::vector<int> a (len);
            for (auto& x : a) x = dist(eng); // FIXME: use std::generate
            return a;
        };
    }

    constexpr auto slow_threshold = 1'000'000;
}

int main(int argc, char **argv)
{
    const auto do_slowest = will_do_slowest(argc, argv);
    auto gen = make_generator();

    const std::vector<std::vector<int>> vs {
        {111, 333, 222},
        {3, 7, 1, 5, 2, -6, 15, 4, 33, -5},
        {9, 9, 1, 8, 3, 0, 2, 0, 7, 15, 4, 3, 3},
        {2, 1},
        {1, 2},
        {5},
        {},
        gen(6),
        gen(1000),
        gen(10'000),
        gen(100'000),
        gen(250'000),
        gen(500'000),
        gen(1'000'000),
        gen(10'000'000),
        gen(100'000'000),
        //gen(1'000'000'000)
    };

    for (const auto& v : vs) {
        std::cout << size(v) << "-element vector";
        print_if_small(v);
        std::cout << ".\n";

        if (size(v) <= slow_threshold) {
            test_insertion_sorts(v);
            if (do_slowest) test_other_slow(v);
        }

        test_fast(v);

        std::cout << '\n';
    }
}
