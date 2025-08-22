//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//
//========================================
package pzcorebus_debug_pkg;
  import  pzcorebus_pkg::*;

  typedef enum bit [10:0] {
    PZCOREBUS_DEBUG_TARGET_READ                   = 11'h001,
    PZCOREBUS_DEBUG_TARGET_WRITE                  = 11'h002,
    PZCOREBUS_DEBUG_TARGET_WRITE_NON_POSTED       = 11'h004,
    PZCOREBUS_DEBUG_TARGET_FULL_WRITE             = 11'h008,
    PZCOREBUS_DEBUG_TARGET_FULL_WRITE_NON_POSTED  = 11'h010,
    PZCOREBUS_DEBUG_TARGET_BROADCAST              = 11'h020,
    PZCOREBUS_DEBUG_TARGET_BROADCAST_NON_POSTED   = 11'h040,
    PZCOREBUS_DEBUG_TARGET_ATOMIC                 = 11'h080,
    PZCOREBUS_DEBUG_TARGET_ATOMIC_NON_POSTED      = 11'h100,
    PZCOREBUS_DEBUG_TARGET_MESSAGE                = 11'h200,
    PZCOREBUS_DEBUG_TARGET_MESSAGE_NON_POSTED     = 11'h400
  } pzcorebus_debug_target;

  typedef bit [$bits(pzcorebus_debug_target)-1:0] pzcorebus_debug_target_command;

  function automatic logic is_target_command(
    pzcorebus_command_type          mcmd,
    pzcorebus_debug_target_command  target_command
  );
    case (mcmd)
      PZCOREBUS_READ:                   return (target_command & PZCOREBUS_DEBUG_TARGET_READ                 ) != '0;
      PZCOREBUS_WRITE:                  return (target_command & PZCOREBUS_DEBUG_TARGET_WRITE                ) != '0;
      PZCOREBUS_WRITE_NON_POSTED:       return (target_command & PZCOREBUS_DEBUG_TARGET_WRITE_NON_POSTED     ) != '0;
      PZCOREBUS_FULL_WRITE:             return (target_command & PZCOREBUS_DEBUG_TARGET_FULL_WRITE           ) != '0;
      PZCOREBUS_FULL_WRITE_NON_POSTED:  return (target_command & PZCOREBUS_DEBUG_TARGET_FULL_WRITE_NON_POSTED) != '0;
      PZCOREBUS_BROADCAST:              return (target_command & PZCOREBUS_DEBUG_TARGET_BROADCAST            ) != '0;
      PZCOREBUS_BROADCAST_NON_POSTED:   return (target_command & PZCOREBUS_DEBUG_TARGET_BROADCAST_NON_POSTED ) != '0;
      PZCOREBUS_ATOMIC:                 return (target_command & PZCOREBUS_DEBUG_TARGET_ATOMIC               ) != '0;
      PZCOREBUS_ATOMIC_NON_POSTED:      return (target_command & PZCOREBUS_DEBUG_TARGET_ATOMIC_NON_POSTED    ) != '0;
      PZCOREBUS_MESSAGE:                return (target_command & PZCOREBUS_DEBUG_TARGET_MESSAGE              ) != '0;
      PZCOREBUS_MESSAGE_NON_POSTED:     return (target_command & PZCOREBUS_DEBUG_TARGET_MESSAGE_NON_POSTED   ) != '0;
      default:                          return '0;
    endcase
  endfunction
endpackage
