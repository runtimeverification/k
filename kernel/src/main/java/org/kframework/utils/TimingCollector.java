// Copyright (c) 2014-2021 K Team. All Rights Reserved.
package org.kframework.utils;

import scala.Tuple2;

import javax.annotation.concurrent.ThreadSafe;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedDeque;

@ThreadSafe
public class TimingCollector {
    final Deque<Tuple2<String, String>> messages = new ConcurrentLinkedDeque<>();

    public void addMessage(String msg, String comparablePart) {
        messages.add(new Tuple2<>(msg, comparablePart));
    }

    public String getOrderedMessages() {
        StringBuilder sb = new StringBuilder();
        List<Tuple2<String, String>> msgList = new ArrayList<>(messages);
        msgList.sort(Comparator.comparing(Tuple2::_2));
        for (Tuple2<String, String> pair : msgList) {
            sb.append(pair._1());
            sb.append("\n");
        }
        return sb.toString();
    }
}
