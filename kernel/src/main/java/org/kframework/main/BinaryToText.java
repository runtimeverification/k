package org.kframework.main;

import com.martiansoftware.nailgun.NGContext;
import org.kframework.kore.K;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.unparser.ToKast;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;

/**
 * Created by dwightguth on 3/29/16.
 */
public class BinaryToText {

    // main method used to decipher binary outputs


    public static void nailMain(NGContext context) throws IOException {
        FileUtil files = new FileUtil(null,null,new File(context.getWorkingDirectory()),null,null,null);
        File f = files.resolveWorkingDirectory(context.getArgs()[0]);
        FileChannel channel = FileChannel.open(f.toPath());
        ByteBuffer buf = channel.map(FileChannel.MapMode.READ_ONLY, 0, channel.size());
        K result = BinaryParser.parse(buf);
        ToKast.apply(result, new PrintStream(new FileOutputStream(files.resolveWorkingDirectory(context.getArgs()[1]))));
    }

    public static void main(String[] args) throws IOException {
        File f = new File(args[0]);
        FileChannel channel = FileChannel.open(f.toPath());
        ByteBuffer buf = channel.map(FileChannel.MapMode.READ_ONLY, 0, channel.size());
        K result = BinaryParser.parse(buf);
        ToKast.apply(result, new PrintStream(new FileOutputStream(new File(args[1]))));
    }
}
