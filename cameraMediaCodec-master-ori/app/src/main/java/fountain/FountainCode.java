package fountain;

import net.fec.openrq.ArrayDataDecoder;
import net.fec.openrq.ArrayDataEncoder;
import net.fec.openrq.EncodingPacket;
import net.fec.openrq.OpenRQ;
import net.fec.openrq.decoder.SourceBlockDecoder;
import net.fec.openrq.encoder.SourceBlockEncoder;
import net.fec.openrq.parameters.FECParameters;

import java.util.LinkedList;

import static net.fec.openrq.parameters.ParameterChecker.maxAllowedDataLength;
import static net.fec.openrq.parameters.ParameterChecker.minDataLength;

/**
 * Created by DELL on 2016/6/24.
 */
public class FountainCode {
    public static final String input="The world’s most advanced forward error correction (FEC) code for data networks, Raptor codes provide protectio" +
            "n against packet loss by sending additional repair data used to reconstruct “erased” or “lost” data. Erasure codes provide data recovery" +
            " by transforming a message into a longer message, allowing the original message to be recovered from a subset of the expanded message. Qualc" +
            "omm® RaptorQ™ forward error correction technology recovers missing data packets with only minimal amounts of additional repair data and with" +
            "out requiring retransmission from the sender. This allows Raptor codes to efficiently and effectively provide reliability in data networks.Luby " +
            "Transform (LT) codes were the first class of efficient practical fountain codes, and were invented in 1998 by Michael Luby. A fountain code can" +
            " generate a potentially unlimited amount of encoded data from the source data, where the source data can be efficiently and completely recovered" +
            " from reception of any combination of encoded data essentially equal in size to the source data. Raptor codes build-on LT codes. They were invent" +
            "ed by Amin Shokrollahi in 2001. For detailed technical information about the origin of Raptor Codes, please refer to  Raptor Codes - IEEE Transacti" +
            "ons On Information Theory.Though advanced at the time, LT codes did not have linear decoding properties. The amount of time needed to decode was mor" +
            "e than linear than the size of the data being decoded. The new concept with Raptor codes is to employ pre-coding to ease the recovery process (and " +
            "speed up decoding). A light-weight pre-coding on the source symbols produces a small fraction of redundant symbols, which added to the source symbo" +
            "ls, become the intermediate symbols. These have the desirable property of being recoverable once most of them are known, using the relationship buil" +
            "t by the pre-coding. The intermediate symbols then become the input of the LT code. With this technique Raptor encoding and decoding take linear tim" +
            "e, meaning the encoding and decoding speed is consistently linearly proportional to the size of the data being decoded across all source block sizes." +
            "An application not using a Raptor forward error correction code typically has to employ protocols that use a lot of feedback and retransmission proto" +
            "cols to enable reliable file delivery or high quality media streaming. These protocols add overheads, require two-way data communication, and can be " +
            "un-scalable. Using a Raptor code, an application can send and receive encoded data, and the fountain properties of the solution obviate, or greatly re" +
            "duce the usage of feedback and retransmission protocols. This allows simpler, more scalable, and more efficient solutions.Raptor technology can be emp" +
            "loyed at the application or transport layer to provide reliability to data communications. Easily integrated into any application, Raptor FEC optimally" +
            " protects streaming media or data distribution applications from the effects of packet loss, regardless of the source of the packet loss. Raptor techn" +
            "oWhether enhancing the quality of streaming content or accelerating the delivery of data, Raptor FEC provides complete flexibility in balancing and opt" +
            "imizing a specific application’s requirements for bandwidth utilization, latency, and degree of packet-loss protection. And because the algorithms em" +
            "ployed by Raptor codes can be implemented as software on relatively low-power platforms, Raptor FEC enables a variety of new applications and services, in" +
            "cluding mobile platforms. For more information on how Raptor codes can be applied to streaming and content delivery solutions please visit our Resources" +
            " page.logy is platform, source and content agnostic.";
    // Fixed value for the payload length
    public static final int PAY_LEN = 1500 - 20 - 8; // UDP-Ipv4 payload length

    // Fixed value for the maximum decoding block size
    public static final int MAX_DEC_MEM = 8 * 1024 * 1024; // 8 MiB

    // The maximum allowed data length, given the parameters above
    private static final long MAX_DATA_LEN = maxAllowedDataLength(PAY_LEN, MAX_DEC_MEM);

    private long DEFAULT_DATALENGTH; //input.getBytes("UTF-8").length;


    /**
     * Returns FEC parameters given a data length.
     *
     * @param dataLen
     *            The length of the source data
     * @return a new instance of <code>FECParameters</code>
     * @throws IllegalArgumentException
     *             If the provided data length is non-positive or surpasses
     *             <code>MAX_DATA_LEN</code>
     */
    public static FECParameters getParameters(long dataLen) {

        if (dataLen < minDataLength())
            throw new IllegalArgumentException("data length is too small");
        if (dataLen > MAX_DATA_LEN)
            throw new IllegalArgumentException("data length is too large");

        return FECParameters.deriveParameters(dataLen, PAY_LEN, MAX_DEC_MEM);
    }
    public static ArrayDataEncoder getEncoder(byte[] data){
        return OpenRQ.newEncoder(data, getParameters((long) data.length));
    }
    public static ArrayDataDecoder getDecoder(long datalen,int overhead){
        return OpenRQ.newDecoder(getParameters(datalen), overhead);
    }
//    public static ArrayDataEncoder getDefaultEncoder(){
//        try{
//            byte[] data=input.getBytes("UTF-8");
//            return getEncoder(data);
//        }catch (java.io.UnsupportedEncodingException e){
//            e.printStackTrace();
//            return null;
//        }
//    }
    public static void main(String[] args) {
        byte[] data=null;
        int datalength=0;
        try{
            data=input.getBytes("UTF-8");
            System.out.println("Input data is ");
//            System.out.println("First letter is :"+(char)data[0]);
//            System.out.println(new String(data,"UTF-8"));

            datalength=data.length;
            System.out.println("Data length is "+datalength);

            FECParameters fecParameters = getParameters((long)datalength);
            System.out.println(fecParameters.numberOfSourceBlocks()+" "+fecParameters.symbolSize()+" "+fecParameters.totalSymbols());

            ArrayDataEncoder arrayDataEncoder = OpenRQ.newEncoder(data, fecParameters);

            LinkedList<byte[]> channel = new LinkedList<byte[]>();

            for(SourceBlockEncoder sourceBlockEncoder: arrayDataEncoder.sourceBlockIterable()){
                for(EncodingPacket encodingPacket: sourceBlockEncoder.sourcePacketsIterable()){
                    channel.add(encodingPacket.asArray());
                }
                int i =0;
                for(EncodingPacket encodingPacket: sourceBlockEncoder.repairPacketsIterable(3)){
                    channel.add(encodingPacket.asArray());
                }
            }

            ArrayDataDecoder arrayDataDecoder = OpenRQ.newDecoderWithOneOverhead(fecParameters);
            for(SourceBlockDecoder sourceBlockDecoder: arrayDataDecoder.sourceBlockIterable()){
                System.out.println(sourceBlockDecoder.numberOfSourceSymbols()+" "+sourceBlockDecoder.isSourceBlockDecoded());
                while(!sourceBlockDecoder.isSourceBlockDecoded()){
                    sourceBlockDecoder.putEncodingPacket(arrayDataDecoder.parsePacket(channel.pop(),false).value());
                }
            }
            if(arrayDataDecoder.isDataDecoded()){
                String result=new String(arrayDataDecoder.dataArray(),"UTF-8");
                System.out.println(result.getBytes("UTF-8").length);
                System.out.println(input.equals(result));
            }

        }catch (java.io.UnsupportedEncodingException e){
            e.printStackTrace();
        }
    }
}
