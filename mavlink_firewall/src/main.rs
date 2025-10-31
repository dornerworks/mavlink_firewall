use mavlink_parser_vest::{
    CommandAck, CommandInt, MavlinkMsg, MavlinkMsgCombinator, MavlinkMsgMsg,
    MavlinkV1MsgCombinatorAlias, MavlinkV2MsgPayload, SpecMavlinkMsg, SpecMavlinkMsgCombinator,
    mavlink_msg, spec_mavlink_msg, spec_mavlink_msg_msg,
};
use vest::buf_traits::From;
use vest::errors::ParseError;
use vest::properties::SecureSpecCombinator;
use vest::properties::{Combinator, SpecCombinator};
use vest::utils::SpecInto;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

// fn print_payload_type(msg: &MavlinkMsg) {
//     match &msg.msg {
//         MavlinkMsgMsg::MavLink1(_) => {}
//         MavlinkMsgMsg::MavLink2(v2_msg) => {
//             let s = match v2_msg.payload {
//                 MavlinkV2MsgPayload::CommandInt(_) => "Command Int",
//                 MavlinkV2MsgPayload::CommandLong(_) => "Command Long",
//                 MavlinkV2MsgPayload::CommandAck(_) => "Command Ack",
//                 MavlinkV2MsgPayload::TerrainRequest(_) => "Terrian Request",
//                 MavlinkV2MsgPayload::Unrecognized(_) => "Unrecognized",
//             };
//             #[verifier::external_body]
//             println!("Payload type: {s} ({})", v2_msg.msgid.as_u32());
//         }
//     }
// }

verus! {

// pub open spec fn spec_parse_packet(packet: &[u8]) -> bool
// {
//     let (len, msg) = spec_mavlink_msg().spec_parse(packet@).unwrap();
//     let a = spec_mavlink_msg().spec_serialize(msg);
//     a == packet@
// }

// fn parse_packet(packet: &[u8]) -> (r: Result<(usize, MavlinkMsg), ParseError>)
//     requires
//         packet.len() >= 30,
//     ensures
//         // spec_mavlink_msg().spec_parse(packet@).is_some() ==> spec_parse_packet(packet),
//         spec_mavlink_msg().spec_parse(packet@).is_none() ==> r.is_err(),

// {
//     let val = mavlink_msg().parse(&packet);


//     // proof { spec_mavlink_msg().theorem_parse_serialize_roundtrip(packet@); }

//     val
// }

fn firewall(packet: &[u8]) -> (r: bool)
    requires
        300 <= packet.len() <= usize::MAX,
    ensures
        match spec_mavlink_msg().spec_parse(packet@) {
            Some((size, val)) => r == !spec_msg_is_flash_bootloader(val),
            None => r == false,
        }
{
    let mut len = 0;
    let mut packet_num = 0;

        match mavlink_msg().parse(packet) {
            Ok((_curr_len, msg)) => {
                can_send(&msg)
            }
            Err(e) => {
                false
            }
        }
}


pub open spec fn spec_msg_is_flash_bootloader(msg: SpecMavlinkMsg) -> bool
{
    (msg.msg is MavLink2 &&
        msg.msg->MavLink2_0.payload is CommandInt &&
        msg.msg->MavLink2_0.payload->CommandInt_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader) ||
    (msg.msg is MavLink2 &&
        msg.msg->MavLink2_0.payload is CommandLong &&
        msg.msg->MavLink2_0.payload->CommandLong_0.command == mavlink_parser_vest::MavCmd::SPEC_FlashBootloader)

}

fn can_send(msg: &MavlinkMsg) -> (r: bool)
    ensures
        spec_msg_is_flash_bootloader(msg@) == (r == false)
{
    match &msg.msg {
        // TODO: Should probably actually handle v1 packets
        MavlinkMsgMsg::MavLink1(_) => true,
        MavlinkMsgMsg::MavLink2(v2_msg) => match &v2_msg.payload {
            MavlinkV2MsgPayload::CommandInt(cmd_int) => {
                cmd_int.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            MavlinkV2MsgPayload::CommandLong(cmd_long) => {
                cmd_long.command != mavlink_parser_vest::MavCmd::FlashBootloader
            }
            _ => true,
        },
    }
}

fn main() {
    let mut packet = [0u8; 300];
    let msg = [
        0xfdu8, 0x13, // |.......+|
        // 0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
        0x00, 0x00, 0x71, 0xff, 0xbe, 0x86, 0x00, 0x00, // |..q.....|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
        0x64, 0x00, 0x2c, 0xc7,
    ];

    let mut i = 0;
    while i < msg.len()
     invariant
        0 <= i <= msg@.len(),
        forall |j| 0 <= j < i ==> packet@[j] == msg@[j],
    decreases
        msg@.len() - i
    {
        packet[i] = msg[i];
        i += 1;
    }
    // packet[0..30].copy_from_slice(&msg[0..30]);

    firewall(&packet);

    // let packet = [
    //     0xfdu8, 0x12, // |.......+|
    //     // 0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
    //     0x00, 0x00, 0x71, 0xff, 0xbe, 0x86, 0x00, 0x00, // |..q.....|
    //     0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
    //     0x31, 0x92, 0x8f, 0x19, 0x7c, 0x40, 0xf6, 0xcc, // |1...|@..|
    //     0x64, 0x00, 0x2c, 0xc7,
    // ];

    // firewall(&packet);

    // let packet = [
    //     0xfdu8, 0x21, // |.......+|
    //     0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
    //     0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x2c, 0xc7,
    // ];

    // firewall(&packet);

    // let packet = [
    //     0xfdu8, 0x21, // |.......+|
    //     0x00, 0x00, 0x71, 0xff, 0xbe, 0x8c, 0x00, 0x00, // |..q.....|
    //     0x31, 0x92, 0x9A, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x2c, 0xc7,
    // ];

    // firewall(&packet);

    // // let packet = [
    // //     0xfdu8, 0x0a, // |.......+|
    // //     0x00, 0x00, 0x71, 0xff, 0xbe, 77, 0x00, 0x00, // |..q.....|
    // //     0x31, 0x92, 0x00, 0x64, 0x00, 0x00, 0x00, 0x00, 0x20, 0x30, 0x2c, 0xc7,
    // // ];

    // // firewall(&packet);

    // let packet = [
    //     0xfdu8, 0x21, // |.......+|
    //     0x00, 0x00, 0x71, 0xff, 0xbe, 0x4c, 0x00, 0x00, // |..q.....|
    //     0x31, 0x92, 0x53, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    //     0x00, 0x00, 0x00, 0x2c, 0xc7,
    // ];

    // firewall(&packet);
}

}
