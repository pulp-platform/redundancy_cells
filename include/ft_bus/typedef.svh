// Copyright (c) 2022 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

`ifndef FT_BUS_TYPEDEF_SVH_
`define FT_BUS_TYPEDEF_SVH_

////////////////////////////////////////////////////////////////////////////////////////////////////
// FT_INTERCO Channel and Request/Response Structs
//
// Usage Example:
// `FT_BUS_TYPEDEF_A_CHAN_T(ft_bus_a_t, ft_bus_addr_t, ft_bus_data_t, ft_bus_be_t, ft_bus_user_t, ft_bus_id_t)
// `FT_BUS_TYPEDEF_R_CHAN_T(ft_bus_r-t, ft_bus_data_t, ft_bus_user_t, ft_bus_id_t)
// `FT_BUS_TYPEDEF_REQ_T(ft_bus_req_t, ft_bus_a_t)
// `FT_BUS_TYPEDEF_RESP_T(ft_bus_resp_t, ft_bus_r_t)
`define FT_BUS_TYPEDEF_A_CHAN_T(ft_bus_a_t, ft_bus_addr_t, ft_bus_data_t, ft_bus_be_t, ft_bus_user_t, ft_bus_id_t) \
  localparam ft_bus_a_t``_AddrBits = ($bits(ft_bus_addr_t)+7) / 8;                          \
  localparam ft_bus_a_t``_BeBits   = ($bits(ft_bus_be_t)+7) / 8;                            \
  localparam ft_bus_a_t``_UserBits = ($bits(ft_bus_user_t)+7) / 8;                          \
  localparam ft_bus_a_t``_IdBits   = ($bits(ft_bus_id_t)+7) / 8;                            \
  typedef struct packed {                                                                             \
    ft_bus_addr_t             addr;                                                 \
    logic [ft_bus_a_t``_AddrBits-1:0] addr_p;                                               \
    logic                     wen;                                                  \
    logic                     wen_p;                                                \
    ft_bus_data_t             wdata_ecc;                                            \
    ft_bus_be_t               be;                                                   \
    logic [  ft_bus_a_t``_BeBits-1:0] be_p;                                                 \
    ft_bus_user_t             user;                                                 \
    logic [ft_bus_a_t``_UserBits-1:0] user_p;                                               \
    ft_bus_id_t               id;                                                   \
    logic [  ft_bus_a_t``_IdBits-1:0] id_p;                                                 \
    logic                     poison;                                               \
  } ft_bus_a_t;
`define FT_BUS_TYPEDEF_R_CHAN_T(ft_bus_r_t, ft_bus_data_t, ft_bus_user_t, ft_bus_id_t) \
  localparam ft_bus_r_t``_UserBits = ($bits(ft_bus_user_t)+7) / 8;                          \
  localparam ft_bus_r_t``_IdBits   = ($bits(ft_bus_id_t)+7) / 8;                            \
  typedef struct packed {                                                              \
    ft_bus_data_t             data_ecc;                              \
    logic                     err;                                   \
    logic                     err_p;                                 \
    ft_bus_user_t             user;                                  \
    logic [ft_bus_r_t``_UserBits-1:0] user_p;                                \
    ft_bus_id_t               id;                                    \
    logic [  ft_bus_r_t``_IdBits-1:0] id_p;                                  \
    logic                     poison;                                \
  } ft_bus_r_t;
`define FT_BUS_TYPEDEF_REQ_T(ft_bus_req_t, ft_bus_a_t) \
  typedef struct packed {                              \
    logic      req;                                    \
    logic      req_p;                                  \
    ft_bus_a_t a;                                      \
  } ft_bus_req_t;
`define FT_BUS_TYPEDEF_RESP_T(ft_bus_resp_t, ft_bus_r_t) \
  typedef struct packed {                                \
    logic      gnt;                                      \
    logic      gnt_p;                                    \
    logic      r_valid;                                  \
    logic      r_valid_p;                                \
    ft_bus_r_t r;                                        \
  } ft_bus_resp_t;
////////////////////////////////////////////////////////////////////////////////////////////////////

`define FT_BUS_TYPEDEF_ALL(__name, __addr_t, __data_t, __be_t, __user_t, __id_t)       \
  `FT_BUS_TYPEDEF_A_CHAN_T(__name``_a_t, __addr_t, __data_t, __be_t, __user_t, __id_t) \
  `FT_BUS_TYPEDEF_R_CHAN_T(__name``_r_t, __data_t, __user_t, __id_t)                   \
  `FT_BUS_TYPEDEF_REQ_T(__name``_req_t, __name``_a_t)                                  \
  `FT_BUS_TYPEDEF_RESP_T(__name``_resp_t, __name``_r_t)

`endif
