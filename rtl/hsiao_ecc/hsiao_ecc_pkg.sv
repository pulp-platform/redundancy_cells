// Copyright 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hsiao ECC package
// Based in part on work by lowRISC

package hsiao_ecc_pkg;

  function automatic int unsigned max_vec(int unsigned vec[], int unsigned size);
    max_vec = 0;
    for (int unsigned i = 0; i < size; i++) begin
      max_vec = vec[i] > max_vec ? vec[i] : max_vec;
    end
  endfunction

  function automatic int unsigned min_vec(int unsigned vec[], int unsigned size);
    min_vec = vec[0];
    for (int unsigned i = 0; i < size; i++) begin
      min_vec = vec[i] < min_vec ? vec[i] : min_vec;
    end
  endfunction

  function automatic int unsigned factorial(int unsigned i);
    // if (i == 1) begin
    //   factorial = 1;
    // end else begin
    //   factorial = i * factorial(i-1);
    // end
    // return factorial;
    factorial = 1;
    for (int unsigned j = i; j > 0; j--) begin
      factorial = factorial * j;
    end
  endfunction

  function automatic int unsigned n_choose_k(int unsigned n, int unsigned k);
    n_choose_k = factorial(n)/(factorial(k)*factorial(n-k));
  endfunction

  function automatic int unsigned ideal_fanin(int unsigned k, int unsigned m);
    int unsigned fanin = 0;
    int unsigned needed = k;
    for (int unsigned select = 3; select < m+1; select += 2) begin
      int unsigned combinations = n_choose_k(m, select);
      if (combinations <= needed) begin
        fanin += (combinations*select+(m-1))/m; // ceil(combinations*select/m)
        needed -= combinations;
      end else begin
        fanin += (needed*select+(m-1))/m; // ceil(needed*select/m)
        needed = 0;
      end
      if (!needed) break;
    end
    return fanin;
  endfunction

  typedef int unsigned combinations_t[][];

  function automatic combinations_t combinations(int unsigned range, int unsigned len);
    int unsigned total_combinations;

    combinations = new [n_choose_k(range, len)];
    for (int unsigned i = 0; i < n_choose_k(range, len); i++) begin
      combinations[i] = new[len];
    end

    for (int unsigned i = 0; i < len; i++) begin
      combinations[0][i] = i;
    end
    total_combinations = n_choose_k(range, len);
    for (int unsigned i = 1; i < total_combinations; i++) begin
      for (int unsigned j = len-1; j >= 0; j--) begin
        if (combinations[i-1][j] + len-j < range) begin
          combinations[i][j] = combinations[i-1][j] + 1;
          for (int unsigned k = 0; k < len; k++) begin
            if (k >= j) begin
              combinations[i][k] = combinations[i][j] + k-j;
            end else begin
              combinations[i][k] = combinations[i-1][k];
            end
          end
          break;
        end
      end
    end
  endfunction

  typedef bit parity_vec_t[][];

  /// Function to generate the Hsiao Code Matrix
  /// k: data bits
  /// m: code bits
  ///
  /// Goal is to find an optimal Hsiao Code Matrix:
  ///   | 1 0 0 0 x x x x |
  ///   | 0 1 0 0 x x x x |
  ///   | 0 0 1 0 x x x x |
  ///   | 0 0 0 1 x x x x |
  /// Then message times matrix => original message with parity
  function automatic parity_vec_t hsiao_matrix(int unsigned k, int unsigned m);
    parity_vec_t existing = new[m];
    combinations_t combs;

    int unsigned needed = k;
    int unsigned max_fanin = ideal_fanin(k, m);
    int unsigned count_index = 0;
    bit comb_added = 0;
    int unsigned tmp_sum = 0;
    int unsigned existing_fanins[] = new[m];
    int unsigned tmp_fanins[]      = new[m];
    int unsigned min_fanin         = 0;
    int unsigned work_fanin        = 0;
    bit comb_used[];

    for (int unsigned i = 0; i < m; i++) begin
      existing[i] = new [k+m];
      for (int unsigned j = 0; j < k+m; j++) begin
        existing[i][j] = '0;
      end
    end


    for (int unsigned step = 3; step < m+1; step += 2) begin
      combs = combinations(m, step);

      if (n_choose_k(m, step) < needed) begin
        // Add all these combinations
        for (int unsigned j = 0; j < n_choose_k(m, step); j++) begin
          for (int unsigned l = 0; l < step; l++) begin
            existing[combs[j][l]][count_index] = 1'b1;
          end
          needed--;
          count_index++;
        end
      end else begin
        // Use subset

        comb_used = new[n_choose_k(m, step)];
        for (int unsigned i = 0; i < n_choose_k(m, step); i++) begin
          comb_used[i] = '0;
        end

        while (needed > 0) begin

          for (int unsigned i = 0; i < m; i++) begin
            existing_fanins[i] = 0;
            for (int unsigned j = 0; j < count_index; j++) begin
              if (existing[i][j]) existing_fanins[i]++;
            end
          end

          comb_added = 0;

          min_fanin = min_vec(existing_fanins, m);

          // First add to increase minimum while keeping max low
          for (int unsigned i = 0; i < n_choose_k(m, step); i++) begin
            if (comb_used[i]) continue;

            for (int unsigned i = 0; i < m; i++) begin
              tmp_fanins[i] = existing_fanins[i];
            end

            for (int unsigned l = 0; l < step; l++) begin
              tmp_fanins[combs[i][l]]++;
            end

            if (min_vec(tmp_fanins, m) > min_fanin && max_vec(tmp_fanins, m) <= work_fanin) begin
              comb_added = 1;
              for (int unsigned l = 0; l < step; l++) begin
                existing[combs[i][l]][count_index] = 1'b1;
              end
              comb_used[i] = 1;
              needed--;
              count_index++;
              break;
            end
          end

          if (comb_added) continue;

          // Then add to increase maximum if previous did not work
          for (int unsigned i = 0; i < n_choose_k(m, step); i++) begin
            if (comb_used[i]) continue;

            for (int unsigned i = 0; i < m; i++) begin
              tmp_fanins[i] = existing_fanins[i];
            end

            for (int unsigned l = 0; l < step; l++) begin
              tmp_fanins[combs[i][l]]++;
            end

            if (max_vec(tmp_fanins, m) <= work_fanin) begin
              comb_added = 1;
              for (int unsigned l = 0; l < step; l++) begin
                existing[combs[i][l]][count_index] = 1'b1;
              end
              comb_used[i] = 1;
              needed--;
              count_index++;
              break;
            end
          end

          if (!comb_added) begin
            work_fanin += 1;
          end
        end
        break;
      end
    end

    if (count_index != k) $error("did not fill all parity bits!");

    for (int unsigned i = 0; i < m; i++) begin
      existing[i][k+i] = 1'b1;
    end

    hsiao_matrix = existing;
  endfunction

  function automatic parity_vec_t transpose(parity_vec_t matrix, int unsigned m, int unsigned n);
    transpose = new[n];
    for (int unsigned i = 0; i < n; i++) begin
      transpose[i] = new[m];
    end
    for (int unsigned i = 0; i < m; i++) begin
      for (int unsigned j = 0; j < n; j++) begin
        transpose[j][i] = matrix[i][j];
      end
    end
  endfunction

endpackage
