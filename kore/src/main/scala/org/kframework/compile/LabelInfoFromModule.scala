package org.kframework.compile

class LabelInfoFromModule(cfgInfo: ConfigurationInfoFromModule) extends LabelInfo {
  cfgInfo.cellLabels.foreach({
    case (sort, label) =>
      addLabel(
        sort.toString,
        label.toString,
        cfgInfo.m.attributesFor(label).contains("assoc"),
        cfgInfo.m.attributesFor(label).contains("comm"))
  })
}
